//! Exact reconstruction of a latent divisor ecology from receiver contact.
//!
//! The production law never receives an integer value, prime name,
//! factorization, gcd, or valuation.  It receives only opaque occurrence
//! identities and returned answers to its own common-generator queries.
//!
//! Pairwise returns first form the one-skeleton of an occurrence contact
//! complex.  Its maximal cliques are only an upper bound: a clique can be
//! assembled from several incompatible generators.  Production therefore
//! queries maximal candidates from the top down.  A positive return closes
//! one latent generator support; a negative return replaces that candidate
//! by its maximal proper faces.  The carried antichain is the unresolved
//! version fiber, not a selected guess.
//!
//! Once every maximal support closes, incidence is reversed.  A set of
//! latent generators is a cell of the dual receiver exactly when at least one
//! occurrence inhabits all of them.  For the arithmetic grading membrane this
//! recovers the squarefree divisor complex up to latent-generator renaming.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    ArithmeticFiberError, ArithmeticFiberStanding, EventId, EventSuccessor, ExactEventLaw,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct DivisorReceiverId(pub u64);

/// An identity local to the contact receiver.
///
/// The arithmetic membrane assigns these in chronology order.  The numeric
/// carrier is an ordinal only; it is not the received integer.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ContactOccurrenceId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct LatentGeneratorId(pub u64);

/// The admitted latent-ecology class.
///
/// `CompleteContactComplex` makes no structural promise and therefore asks
/// enough higher-order questions to determine every maximal contact face.
/// `PrivateWitnessedGeneratorFacets` declares that every irredundant latent
/// generator has at least one occurrence which inhabits no other generator.
/// That invariant does not identify the witness.  Production must find and
/// certify its closed receiver neighborhood.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum DivisorReconstructionDoctrine {
    CompleteContactComplex,
    PrivateWitnessedGeneratorFacets,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum DivisorContactQueryPurpose {
    PairwiseSkeleton,
    FacetDiscrimination,
}

/// One production-owned receiver question.
///
/// `common_generator` asks whether every listed occurrence shares at least
/// one latent generator.  Members are canonical receiver ordinals.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct DivisorContactQuery {
    pub receiver: DivisorReceiverId,
    pub members: Vec<ContactOccurrenceId>,
    pub purpose: DivisorContactQueryPurpose,
}

impl DivisorContactQuery {
    fn new(
        receiver: DivisorReceiverId,
        members: Vec<ContactOccurrenceId>,
        purpose: DivisorContactQueryPurpose,
    ) -> Result<Self, DivisorReconstructionError> {
        let query = Self {
            receiver,
            members,
            purpose,
        };
        query.validate()?;
        Ok(query)
    }

    fn validate(&self) -> Result<(), DivisorReconstructionError> {
        if self.members.len() < 2
            || self.members.windows(2).any(|pair| pair[0] >= pair[1])
            || matches!(
                (self.purpose, self.members.len()),
                (DivisorContactQueryPurpose::PairwiseSkeleton, length) if length != 2
            )
            || matches!(
                (self.purpose, self.members.len()),
                (DivisorContactQueryPurpose::FacetDiscrimination, length) if length < 3
            )
        {
            return Err(DivisorReconstructionError::MalformedQuery(self.clone()));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DivisorContactTestimony {
    pub event: EventId,
    pub query: DivisorContactQuery,
    pub common_generator: bool,
}

/// Exact unresolved reconstruction family.
///
/// Positive sections must inhabit every compatible occurrence complex.
/// Negative fronts may inhabit none.  Before pairwise closure, the named
/// missing pairs are still free coordinates.  Afterwards,
/// `unresolved_maximal_supports` is the current upper antichain: each member
/// either closes as one generator support or separates into proper faces.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DivisorContactVersionFiber {
    pub schema: String,
    pub receiver: DivisorReceiverId,
    pub doctrine: DivisorReconstructionDoctrine,
    pub occurrence_count: u64,
    pub positive_sections: BTreeSet<Vec<ContactOccurrenceId>>,
    pub negative_fronts: BTreeSet<Vec<ContactOccurrenceId>>,
    pub unreturned_pair_count: u64,
    pub confirmed_generator_supports: Vec<Vec<ContactOccurrenceId>>,
    pub unresolved_maximal_supports: Vec<Vec<ContactOccurrenceId>>,
    pub doctrine_obstructed: bool,
}

impl DivisorContactVersionFiber {
    pub fn is_unique(&self) -> bool {
        self.unreturned_pair_count == 0
            && self.unresolved_maximal_supports.is_empty()
            && !self.doctrine_obstructed
    }
}

/// Exact failure of the private-witness doctrine.
///
/// The returned pairwise ecology requires contact which none of the
/// receiver-neighborhood generator facets can carry.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrivateGeneratorWitnessObstruction {
    pub schema: String,
    pub receiver: DivisorReceiverId,
    pub uncovered_occurrences: Vec<ContactOccurrenceId>,
    pub uncovered_positive_pairs: Vec<Vec<ContactOccurrenceId>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReconstructedBoundaryTerm {
    pub generators: Vec<LatentGeneratorId>,
    pub hand: i8,
}

/// One cell of the generator-side divisor receiver.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReconstructedGeneratorCell {
    pub generators: Vec<LatentGeneratorId>,
    pub grade: u32,
    pub witness_occurrences: Vec<ContactOccurrenceId>,
    pub boundary: Vec<ReconstructedBoundaryTerm>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LatentGeneratorSupport {
    pub generator: LatentGeneratorId,
    pub occurrences: Vec<ContactOccurrenceId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LatentContactCompression {
    pub occurrence_count: u64,
    pub latent_generator_count: u64,
    /// Incidences retained by the factored latent representation.
    pub support_memberships: u64,
    /// Positive pair contacts reproduced by expanding those incidences.
    pub expanded_positive_pair_contacts: u64,
    pub all_pair_slots: u64,
}

/// Unique dual-receiver reconstruction, modulo latent-generator names.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DivisorReconstructionCertificate {
    pub schema: String,
    pub receiver: DivisorReceiverId,
    pub chronology: Vec<ContactOccurrenceId>,
    pub generator_supports: Vec<LatentGeneratorSupport>,
    pub occurrence_memberships: BTreeMap<ContactOccurrenceId, Vec<LatentGeneratorId>>,
    pub generator_cells: Vec<ReconstructedGeneratorCell>,
    pub compression: LatentContactCompression,
}

impl DivisorReconstructionCertificate {
    /// Reproduce any occurrence-side common-generator contact from the
    /// compressed latent supports.
    pub fn predicts_contact(
        &self,
        members: &[ContactOccurrenceId],
    ) -> Result<bool, DivisorReconstructionError> {
        if members.is_empty()
            || members.windows(2).any(|pair| pair[0] >= pair[1])
            || members
                .iter()
                .any(|member| !self.occurrence_memberships.contains_key(member))
        {
            return Err(DivisorReconstructionError::MalformedContactSection(
                members.to_vec(),
            ));
        }
        Ok(self
            .generator_supports
            .iter()
            .any(|support| is_subset(members, &support.occurrences)))
    }

    pub fn generator_f_vector(&self) -> BTreeMap<u32, u64> {
        let mut result = BTreeMap::new();
        for cell in &self.generator_cells {
            *result.entry(cell.grade).or_default() += 1;
        }
        result
    }

    pub fn generator_boundary_squared_zero(&self) -> bool {
        self.generator_cells.iter().all(|cell| {
            if cell.generators.len() < 3 {
                return true;
            }
            let mut coefficients = BTreeMap::<Vec<LatentGeneratorId>, i16>::new();
            for outer in &cell.boundary {
                for removed in 0..outer.generators.len() {
                    let mut face = outer.generators.clone();
                    face.remove(removed);
                    let inner_hand = if removed % 2 == 0 { 1_i16 } else { -1_i16 };
                    *coefficients.entry(face).or_default() += i16::from(outer.hand) * inner_hand;
                }
            }
            coefficients.values().all(|coefficient| *coefficient == 0)
        })
    }

    pub fn validate(&self) -> Result<(), DivisorReconstructionError> {
        if self.schema != "holonic-engine.divisor-reconstruction-certificate.v1"
            || self.chronology.is_empty()
            || self.chronology.windows(2).any(|pair| pair[0] >= pair[1])
        {
            return Err(DivisorReconstructionError::MalformedCertificate);
        }
        if !self.generator_boundary_squared_zero() {
            return Err(DivisorReconstructionError::MalformedCertificate);
        }
        let supports = self
            .generator_supports
            .iter()
            .map(|support| support.occurrences.clone())
            .collect::<Vec<_>>();
        if supports.is_empty()
            || supports.windows(2).any(|pair| pair[0] >= pair[1])
            || supports.iter().any(|support| {
                support.is_empty()
                    || support.windows(2).any(|pair| pair[0] >= pair[1])
                    || support
                        .iter()
                        .any(|member| self.chronology.binary_search(member).is_err())
            })
            || supports.iter().enumerate().any(|(left_index, left)| {
                supports
                    .iter()
                    .enumerate()
                    .any(|(right_index, right)| left_index != right_index && is_subset(left, right))
            })
        {
            return Err(DivisorReconstructionError::MalformedCertificate);
        }
        for (index, support) in self.generator_supports.iter().enumerate() {
            let expected =
                u64::try_from(index).map_err(|_| DivisorReconstructionError::CarrierOverflow)?;
            if support.generator != LatentGeneratorId(expected) {
                return Err(DivisorReconstructionError::MalformedCertificate);
            }
        }
        let expected = build_certificate(self.receiver, &self.chronology, supports)?;
        if &expected != self {
            return Err(DivisorReconstructionError::MalformedCertificate);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct DivisorReconstructionWork {
    pub pairwise_returns: u64,
    pub higher_order_returns: u64,
    pub maximal_clique_search_nodes: u64,
    pub witness_neighborhood_checks: u64,
    pub negative_candidate_splits: u64,
    pub rejected_witness_candidates: u64,
    pub implicit_atomic_facets: u64,
}

impl DivisorReconstructionWork {
    fn checked_difference(&self, earlier: &Self) -> Result<Self, DivisorReconstructionError> {
        Ok(Self {
            pairwise_returns: self
                .pairwise_returns
                .checked_sub(earlier.pairwise_returns)
                .ok_or(DivisorReconstructionError::CarrierOverflow)?,
            higher_order_returns: self
                .higher_order_returns
                .checked_sub(earlier.higher_order_returns)
                .ok_or(DivisorReconstructionError::CarrierOverflow)?,
            maximal_clique_search_nodes: self
                .maximal_clique_search_nodes
                .checked_sub(earlier.maximal_clique_search_nodes)
                .ok_or(DivisorReconstructionError::CarrierOverflow)?,
            witness_neighborhood_checks: self
                .witness_neighborhood_checks
                .checked_sub(earlier.witness_neighborhood_checks)
                .ok_or(DivisorReconstructionError::CarrierOverflow)?,
            negative_candidate_splits: self
                .negative_candidate_splits
                .checked_sub(earlier.negative_candidate_splits)
                .ok_or(DivisorReconstructionError::CarrierOverflow)?,
            rejected_witness_candidates: self
                .rejected_witness_candidates
                .checked_sub(earlier.rejected_witness_candidates)
                .ok_or(DivisorReconstructionError::CarrierOverflow)?,
            implicit_atomic_facets: self
                .implicit_atomic_facets
                .checked_sub(earlier.implicit_atomic_facets)
                .ok_or(DivisorReconstructionError::CarrierOverflow)?,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DivisorReconstructionStanding {
    pub schema: String,
    receiver: Option<DivisorReceiverId>,
    doctrine: Option<DivisorReconstructionDoctrine>,
    chronology: Vec<ContactOccurrenceId>,
    founding_event: Option<EventId>,
    history: Vec<DivisorContactTestimony>,
    pair_responses: BTreeMap<Vec<ContactOccurrenceId>, bool>,
    higher_responses: BTreeMap<Vec<ContactOccurrenceId>, bool>,
    confirmed_supports: BTreeSet<Vec<ContactOccurrenceId>>,
    unresolved_supports: BTreeSet<Vec<ContactOccurrenceId>>,
    facet_search_started: bool,
    next_query: Option<DivisorContactQuery>,
    version_fiber: Option<DivisorContactVersionFiber>,
    certificate: Option<DivisorReconstructionCertificate>,
    obstruction: Option<PrivateGeneratorWitnessObstruction>,
    work: DivisorReconstructionWork,
    used_events: BTreeSet<EventId>,
}

impl Default for DivisorReconstructionStanding {
    fn default() -> Self {
        Self {
            schema: "holonic-engine.divisor-reconstruction-standing.v1".to_owned(),
            receiver: None,
            doctrine: None,
            chronology: Vec::new(),
            founding_event: None,
            history: Vec::new(),
            pair_responses: BTreeMap::new(),
            higher_responses: BTreeMap::new(),
            confirmed_supports: BTreeSet::new(),
            unresolved_supports: BTreeSet::new(),
            facet_search_started: false,
            next_query: None,
            version_fiber: None,
            certificate: None,
            obstruction: None,
            work: DivisorReconstructionWork::default(),
            used_events: BTreeSet::new(),
        }
    }
}

impl DivisorReconstructionStanding {
    pub fn receiver(&self) -> Option<DivisorReceiverId> {
        self.receiver
    }

    pub fn doctrine(&self) -> Option<DivisorReconstructionDoctrine> {
        self.doctrine
    }

    pub fn chronology(&self) -> &[ContactOccurrenceId] {
        &self.chronology
    }

    pub fn history(&self) -> &[DivisorContactTestimony] {
        &self.history
    }

    pub fn next_query(&self) -> Option<&DivisorContactQuery> {
        self.next_query.as_ref()
    }

    pub fn version_fiber(&self) -> Option<&DivisorContactVersionFiber> {
        self.version_fiber.as_ref()
    }

    pub fn certificate(&self) -> Option<&DivisorReconstructionCertificate> {
        self.certificate.as_ref()
    }

    pub fn obstruction(&self) -> Option<&PrivateGeneratorWitnessObstruction> {
        self.obstruction.as_ref()
    }

    pub fn work(&self) -> &DivisorReconstructionWork {
        &self.work
    }

    pub fn validate(&self) -> Result<(), DivisorReconstructionError> {
        self.validate_incremental()?;
        let Some(receiver) = self.receiver else {
            if self != &Self::default() {
                return Err(DivisorReconstructionError::MalformedStanding);
            }
            return Ok(());
        };
        let founding_event = self
            .founding_event
            .ok_or(DivisorReconstructionError::MalformedStanding)?;
        let doctrine = self
            .doctrine
            .ok_or(DivisorReconstructionError::MalformedStanding)?;
        let mut replay = Self::default();
        replay.apply_founding(founding_event, receiver, doctrine, self.chronology.clone())?;
        for testimony in &self.history {
            replay.apply_testimony(testimony.clone())?;
        }
        if replay != *self {
            return Err(DivisorReconstructionError::MalformedStanding);
        }
        Ok(())
    }

    fn validate_incremental(&self) -> Result<(), DivisorReconstructionError> {
        if self.schema != "holonic-engine.divisor-reconstruction-standing.v1" {
            return Err(DivisorReconstructionError::MalformedStanding);
        }
        let Some(receiver) = self.receiver else {
            return if self == &Self::default() {
                Ok(())
            } else {
                Err(DivisorReconstructionError::MalformedStanding)
            };
        };
        let doctrine = self
            .doctrine
            .ok_or(DivisorReconstructionError::MalformedStanding)?;
        if self.chronology.is_empty()
            || self.chronology.windows(2).any(|pair| pair[0] >= pair[1])
            || self.founding_event.is_none()
        {
            return Err(DivisorReconstructionError::MalformedStanding);
        }
        let mut history_pairs = BTreeMap::new();
        let mut history_higher = BTreeMap::new();
        let mut events = BTreeSet::from([self
            .founding_event
            .ok_or(DivisorReconstructionError::MalformedStanding)?]);
        for testimony in &self.history {
            testimony.query.validate()?;
            if testimony.query.receiver != receiver
                || testimony
                    .query
                    .members
                    .iter()
                    .any(|member| self.chronology.binary_search(member).is_err())
                || !events.insert(testimony.event)
            {
                return Err(DivisorReconstructionError::MalformedStanding);
            }
            let target = match testimony.query.purpose {
                DivisorContactQueryPurpose::PairwiseSkeleton => &mut history_pairs,
                DivisorContactQueryPurpose::FacetDiscrimination => &mut history_higher,
            };
            if target
                .insert(testimony.query.members.clone(), testimony.common_generator)
                .is_some()
            {
                return Err(DivisorReconstructionError::MalformedStanding);
            }
        }
        if history_pairs != self.pair_responses
            || history_higher != self.higher_responses
            || events != self.used_events
            || self.work.pairwise_returns
                != u64::try_from(self.pair_responses.len())
                    .map_err(|_| DivisorReconstructionError::CarrierOverflow)?
            || self.work.higher_order_returns
                != u64::try_from(self.higher_responses.len())
                    .map_err(|_| DivisorReconstructionError::CarrierOverflow)?
            || self.work.negative_candidate_splits
                != u64::try_from(
                    self.higher_responses
                        .values()
                        .filter(|response| {
                            !**response
                                && doctrine
                                    == DivisorReconstructionDoctrine::CompleteContactComplex
                        })
                        .count(),
                )
                .map_err(|_| DivisorReconstructionError::CarrierOverflow)?
            || self.work.rejected_witness_candidates
                != u64::try_from(
                    self.higher_responses
                        .values()
                        .filter(|response| {
                            !**response
                                && doctrine
                                    == DivisorReconstructionDoctrine::PrivateWitnessedGeneratorFacets
                        })
                        .count(),
                )
                .map_err(|_| DivisorReconstructionError::CarrierOverflow)?
        {
            return Err(DivisorReconstructionError::MalformedStanding);
        }
        let returned_pair_count = self.pair_responses.len();
        let expected_pair_prefix = ordered_pairs(&self.chronology)
            .into_iter()
            .take(returned_pair_count)
            .collect::<BTreeSet<_>>();
        if self.pair_responses.keys().cloned().collect::<BTreeSet<_>>() != expected_pair_prefix {
            return Err(DivisorReconstructionError::MalformedStanding);
        }
        let expected_query =
            if let Some(pair) = first_missing_pair(&self.chronology, &self.pair_responses) {
                if self.facet_search_started
                    || !self.higher_responses.is_empty()
                    || !self.confirmed_supports.is_empty()
                    || !self.unresolved_supports.is_empty()
                    || self.certificate.is_some()
                    || self.obstruction.is_some()
                {
                    return Err(DivisorReconstructionError::MalformedStanding);
                }
                Some(DivisorContactQuery::new(
                    receiver,
                    pair,
                    DivisorContactQueryPurpose::PairwiseSkeleton,
                )?)
            } else if let Some(candidate) = next_facet_candidate(&self.unresolved_supports) {
                if !self.facet_search_started
                    || self.certificate.is_some()
                    || self.obstruction.is_some()
                {
                    return Err(DivisorReconstructionError::MalformedStanding);
                }
                Some(DivisorContactQuery::new(
                    receiver,
                    candidate,
                    DivisorContactQueryPurpose::FacetDiscrimination,
                )?)
            } else {
                if !self.facet_search_started
                    || (self.certificate.is_none() == self.obstruction.is_none())
                {
                    return Err(DivisorReconstructionError::MalformedStanding);
                }
                None
            };
        if self.next_query != expected_query {
            return Err(DivisorReconstructionError::MalformedStanding);
        }
        if let Some(query) = &self.next_query {
            query.validate()?;
            if query.receiver != receiver
                || query
                    .members
                    .iter()
                    .any(|member| self.chronology.binary_search(member).is_err())
            {
                return Err(DivisorReconstructionError::MalformedStanding);
            }
        }
        let expected_fiber = derive_version_fiber(self)?;
        if self.version_fiber.as_ref() != Some(&expected_fiber) {
            return Err(DivisorReconstructionError::MalformedStanding);
        }
        match &self.certificate {
            Some(certificate) => {
                certificate.validate()?;
                if self.next_query.is_some()
                    || !self.unresolved_supports.is_empty()
                    || !self.facet_search_started
                    || self.obstruction.is_some()
                    || certificate.receiver != receiver
                    || certificate
                        .generator_supports
                        .iter()
                        .map(|support| support.occurrences.clone())
                        .collect::<BTreeSet<_>>()
                        != self.confirmed_supports
                {
                    return Err(DivisorReconstructionError::MalformedStanding);
                }
            }
            None => {
                if self.next_query.is_none() && self.obstruction.is_none() {
                    return Err(DivisorReconstructionError::MalformedStanding);
                }
            }
        }
        if let Some(obstruction) = &self.obstruction
            && (doctrine != DivisorReconstructionDoctrine::PrivateWitnessedGeneratorFacets
                || obstruction.receiver != receiver
                || obstruction.uncovered_occurrences.is_empty()
                    && obstruction.uncovered_positive_pairs.is_empty())
        {
            return Err(DivisorReconstructionError::MalformedStanding);
        }
        Ok(())
    }

    fn apply_founding(
        &mut self,
        event: EventId,
        receiver: DivisorReceiverId,
        doctrine: DivisorReconstructionDoctrine,
        chronology: Vec<ContactOccurrenceId>,
    ) -> Result<(), DivisorReconstructionError> {
        if self.receiver.is_some() {
            return Err(DivisorReconstructionError::ReceiverAlreadyFounded);
        }
        if chronology.is_empty() || chronology.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(DivisorReconstructionError::MalformedChronology);
        }
        self.receiver = Some(receiver);
        self.doctrine = Some(doctrine);
        self.chronology = chronology;
        self.founding_event = Some(event);
        self.used_events.insert(event);
        self.settle()?;
        Ok(())
    }

    fn apply_testimony(
        &mut self,
        testimony: DivisorContactTestimony,
    ) -> Result<(), DivisorReconstructionError> {
        if self.used_events.contains(&testimony.event) {
            return Err(DivisorReconstructionError::RepeatedEvent(testimony.event));
        }
        testimony.query.validate()?;
        if self.next_query.as_ref() != Some(&testimony.query) {
            return Err(DivisorReconstructionError::UnexpectedReturnedQuery {
                expected: self.next_query.clone(),
                received: testimony.query,
            });
        }
        let members = testimony.query.members.clone();
        match testimony.query.purpose {
            DivisorContactQueryPurpose::PairwiseSkeleton => {
                if self
                    .pair_responses
                    .insert(members, testimony.common_generator)
                    .is_some()
                {
                    return Err(DivisorReconstructionError::RepeatedContactSection);
                }
                self.work.pairwise_returns = self
                    .work
                    .pairwise_returns
                    .checked_add(1)
                    .ok_or(DivisorReconstructionError::CarrierOverflow)?;
            }
            DivisorContactQueryPurpose::FacetDiscrimination => {
                if !self.unresolved_supports.remove(&members)
                    || self
                        .higher_responses
                        .insert(members.clone(), testimony.common_generator)
                        .is_some()
                {
                    return Err(DivisorReconstructionError::RepeatedContactSection);
                }
                self.work.higher_order_returns = self
                    .work
                    .higher_order_returns
                    .checked_add(1)
                    .ok_or(DivisorReconstructionError::CarrierOverflow)?;
                if testimony.common_generator {
                    self.confirmed_supports.insert(members);
                } else {
                    match self
                        .doctrine
                        .ok_or(DivisorReconstructionError::MalformedStanding)?
                    {
                        DivisorReconstructionDoctrine::CompleteContactComplex => {
                            self.work.negative_candidate_splits = self
                                .work
                                .negative_candidate_splits
                                .checked_add(1)
                                .ok_or(DivisorReconstructionError::CarrierOverflow)?;
                            for removed in 0..members.len() {
                                let mut face = members.clone();
                                face.remove(removed);
                                if !face.is_empty() {
                                    self.unresolved_supports.insert(face);
                                }
                            }
                        }
                        DivisorReconstructionDoctrine::PrivateWitnessedGeneratorFacets => {
                            self.work.rejected_witness_candidates = self
                                .work
                                .rejected_witness_candidates
                                .checked_add(1)
                                .ok_or(DivisorReconstructionError::CarrierOverflow)?;
                        }
                    }
                }
            }
        }
        self.used_events.insert(testimony.event);
        self.history.push(testimony);
        self.settle()?;
        Ok(())
    }

    fn settle(&mut self) -> Result<(), DivisorReconstructionError> {
        let receiver = self
            .receiver
            .ok_or(DivisorReconstructionError::MalformedStanding)?;
        let doctrine = self
            .doctrine
            .ok_or(DivisorReconstructionError::MalformedStanding)?;
        if let Some(pair) = first_missing_pair(&self.chronology, &self.pair_responses) {
            self.next_query = Some(DivisorContactQuery::new(
                receiver,
                pair,
                DivisorContactQueryPurpose::PairwiseSkeleton,
            )?);
            self.refresh_derived()?;
            return Ok(());
        }

        if !self.facet_search_started {
            match doctrine {
                DivisorReconstructionDoctrine::CompleteContactComplex => {
                    let (cliques, search_nodes) =
                        maximal_pairwise_cliques(&self.chronology, &self.pair_responses)?;
                    self.unresolved_supports = cliques;
                    self.work.maximal_clique_search_nodes = self
                        .work
                        .maximal_clique_search_nodes
                        .checked_add(search_nodes)
                        .ok_or(DivisorReconstructionError::CarrierOverflow)?;
                }
                DivisorReconstructionDoctrine::PrivateWitnessedGeneratorFacets => {
                    let (candidates, checks) =
                        private_witness_candidates(&self.chronology, &self.pair_responses)?;
                    self.unresolved_supports = candidates;
                    self.work.witness_neighborhood_checks = self
                        .work
                        .witness_neighborhood_checks
                        .checked_add(checks)
                        .ok_or(DivisorReconstructionError::CarrierOverflow)?;
                }
            }
            self.facet_search_started = true;
        }

        loop {
            match doctrine {
                DivisorReconstructionDoctrine::CompleteContactComplex => {
                    normalize_antichain(&mut self.unresolved_supports, &self.confirmed_supports);
                }
                DivisorReconstructionDoctrine::PrivateWitnessedGeneratorFacets => {
                    normalize_witness_candidates(
                        &mut self.unresolved_supports,
                        &self.confirmed_supports,
                    );
                }
            }
            let atomic = self
                .unresolved_supports
                .iter()
                .filter(|support| support.len() <= 2)
                .cloned()
                .collect::<Vec<_>>();
            if atomic.is_empty() {
                break;
            }
            for support in atomic {
                self.unresolved_supports.remove(&support);
                self.confirmed_supports.insert(support);
                self.work.implicit_atomic_facets = self
                    .work
                    .implicit_atomic_facets
                    .checked_add(1)
                    .ok_or(DivisorReconstructionError::CarrierOverflow)?;
            }
        }

        if let Some(candidate) = next_facet_candidate(&self.unresolved_supports) {
            self.next_query = Some(DivisorContactQuery::new(
                receiver,
                candidate,
                DivisorContactQueryPurpose::FacetDiscrimination,
            )?);
            self.certificate = None;
            self.obstruction = None;
        } else {
            self.next_query = None;
            match doctrine {
                DivisorReconstructionDoctrine::CompleteContactComplex => {
                    self.obstruction = None;
                    self.certificate = Some(build_certificate(
                        receiver,
                        &self.chronology,
                        self.confirmed_supports.iter().cloned().collect(),
                    )?);
                }
                DivisorReconstructionDoctrine::PrivateWitnessedGeneratorFacets => {
                    self.obstruction = private_witness_obstruction(
                        receiver,
                        &self.chronology,
                        &self.pair_responses,
                        &self.confirmed_supports,
                    );
                    self.certificate = if self.obstruction.is_none() {
                        Some(build_certificate(
                            receiver,
                            &self.chronology,
                            self.confirmed_supports.iter().cloned().collect(),
                        )?)
                    } else {
                        None
                    };
                }
            }
        }
        self.refresh_derived()?;
        Ok(())
    }

    fn refresh_derived(&mut self) -> Result<(), DivisorReconstructionError> {
        self.version_fiber = Some(derive_version_fiber(self)?);
        Ok(())
    }
}

fn derive_version_fiber(
    standing: &DivisorReconstructionStanding,
) -> Result<DivisorContactVersionFiber, DivisorReconstructionError> {
    let receiver = standing
        .receiver
        .ok_or(DivisorReconstructionError::MalformedStanding)?;
    let doctrine = standing
        .doctrine
        .ok_or(DivisorReconstructionError::MalformedStanding)?;
    let mut positive_sections = standing
        .chronology
        .iter()
        .map(|member| vec![*member])
        .collect::<BTreeSet<_>>();
    positive_sections.extend(
        standing
            .pair_responses
            .iter()
            .chain(&standing.higher_responses)
            .filter_map(|(members, response)| response.then_some(members.clone())),
    );
    let negative_sections = standing
        .pair_responses
        .iter()
        .chain(&standing.higher_responses)
        .filter_map(|(members, response)| (!response).then_some(members.clone()))
        .collect::<BTreeSet<_>>();
    let negative_fronts = negative_sections
        .iter()
        .filter(|candidate| {
            !negative_sections
                .iter()
                .any(|other| other.len() < candidate.len() && is_subset(other, candidate))
        })
        .cloned()
        .collect();
    let pair_slots = pair_slot_count(standing.chronology.len())?;
    let returned_pairs = u64::try_from(standing.pair_responses.len())
        .map_err(|_| DivisorReconstructionError::CarrierOverflow)?;
    Ok(DivisorContactVersionFiber {
        schema: "holonic-engine.divisor-contact-version-fiber.v1".to_owned(),
        receiver,
        doctrine,
        occurrence_count: u64::try_from(standing.chronology.len())
            .map_err(|_| DivisorReconstructionError::CarrierOverflow)?,
        positive_sections,
        negative_fronts,
        unreturned_pair_count: pair_slots
            .checked_sub(returned_pairs)
            .ok_or(DivisorReconstructionError::CarrierOverflow)?,
        confirmed_generator_supports: standing.confirmed_supports.iter().cloned().collect(),
        unresolved_maximal_supports: standing.unresolved_supports.iter().cloned().collect(),
        doctrine_obstructed: standing.obstruction.is_some(),
    })
}

fn pair_slot_count(population: usize) -> Result<u64, DivisorReconstructionError> {
    let population =
        u64::try_from(population).map_err(|_| DivisorReconstructionError::CarrierOverflow)?;
    population
        .checked_mul(population.saturating_sub(1))
        .and_then(|product| product.checked_div(2))
        .ok_or(DivisorReconstructionError::CarrierOverflow)
}

fn first_missing_pair(
    chronology: &[ContactOccurrenceId],
    responses: &BTreeMap<Vec<ContactOccurrenceId>, bool>,
) -> Option<Vec<ContactOccurrenceId>> {
    for left in 0..chronology.len() {
        for right in left + 1..chronology.len() {
            let pair = vec![chronology[left], chronology[right]];
            if !responses.contains_key(&pair) {
                return Some(pair);
            }
        }
    }
    None
}

fn ordered_pairs(chronology: &[ContactOccurrenceId]) -> Vec<Vec<ContactOccurrenceId>> {
    let mut pairs = Vec::new();
    for left in 0..chronology.len() {
        for right in left + 1..chronology.len() {
            pairs.push(vec![chronology[left], chronology[right]]);
        }
    }
    pairs
}

fn maximal_pairwise_cliques(
    chronology: &[ContactOccurrenceId],
    responses: &BTreeMap<Vec<ContactOccurrenceId>, bool>,
) -> Result<(BTreeSet<Vec<ContactOccurrenceId>>, u64), DivisorReconstructionError> {
    let mut adjacency = chronology
        .iter()
        .map(|member| (*member, BTreeSet::new()))
        .collect::<BTreeMap<_, _>>();
    for (pair, response) in responses {
        if pair.len() != 2 {
            return Err(DivisorReconstructionError::MalformedStanding);
        }
        if *response {
            adjacency
                .get_mut(&pair[0])
                .ok_or(DivisorReconstructionError::MalformedStanding)?
                .insert(pair[1]);
            adjacency
                .get_mut(&pair[1])
                .ok_or(DivisorReconstructionError::MalformedStanding)?
                .insert(pair[0]);
        }
    }
    let mut cliques = BTreeSet::new();
    let mut search_nodes = 0_u64;
    bron_kerbosch(
        BTreeSet::new(),
        chronology.iter().copied().collect(),
        BTreeSet::new(),
        &adjacency,
        &mut cliques,
        &mut search_nodes,
    )?;
    Ok((cliques, search_nodes))
}

fn private_witness_candidates(
    chronology: &[ContactOccurrenceId],
    responses: &BTreeMap<Vec<ContactOccurrenceId>, bool>,
) -> Result<(BTreeSet<Vec<ContactOccurrenceId>>, u64), DivisorReconstructionError> {
    let mut adjacency = chronology
        .iter()
        .map(|member| (*member, BTreeSet::new()))
        .collect::<BTreeMap<_, _>>();
    for (pair, response) in responses {
        if pair.len() != 2 {
            return Err(DivisorReconstructionError::MalformedStanding);
        }
        if *response {
            adjacency
                .get_mut(&pair[0])
                .ok_or(DivisorReconstructionError::MalformedStanding)?
                .insert(pair[1]);
            adjacency
                .get_mut(&pair[1])
                .ok_or(DivisorReconstructionError::MalformedStanding)?
                .insert(pair[0]);
        }
    }
    let mut candidates = BTreeSet::new();
    let mut checks = 0_u64;
    for occurrence in chronology {
        checks = checks
            .checked_add(1)
            .ok_or(DivisorReconstructionError::CarrierOverflow)?;
        let mut neighborhood = adjacency[occurrence].clone();
        neighborhood.insert(*occurrence);
        let members = neighborhood.iter().copied().collect::<Vec<_>>();
        let is_clique = members.iter().enumerate().all(|(left_index, left)| {
            members[left_index + 1..]
                .iter()
                .all(|right| adjacency[left].contains(right))
        });
        if is_clique {
            candidates.insert(members);
        }
    }
    Ok((candidates, checks))
}

fn bron_kerbosch(
    current: BTreeSet<ContactOccurrenceId>,
    mut possible: BTreeSet<ContactOccurrenceId>,
    mut excluded: BTreeSet<ContactOccurrenceId>,
    adjacency: &BTreeMap<ContactOccurrenceId, BTreeSet<ContactOccurrenceId>>,
    cliques: &mut BTreeSet<Vec<ContactOccurrenceId>>,
    search_nodes: &mut u64,
) -> Result<(), DivisorReconstructionError> {
    *search_nodes = search_nodes
        .checked_add(1)
        .ok_or(DivisorReconstructionError::CarrierOverflow)?;
    if possible.is_empty() && excluded.is_empty() {
        cliques.insert(current.iter().copied().collect());
        return Ok(());
    }
    let pivot = possible.union(&excluded).copied().max_by(|left, right| {
        let left_count = possible.intersection(&adjacency[left]).count();
        let right_count = possible.intersection(&adjacency[right]).count();
        left_count.cmp(&right_count).then_with(|| right.cmp(left))
    });
    let pivot_neighbors = pivot
        .map(|pivot| adjacency[&pivot].clone())
        .unwrap_or_default();
    let branches = possible
        .difference(&pivot_neighbors)
        .copied()
        .collect::<Vec<_>>();
    for vertex in branches {
        let mut next_current = current.clone();
        next_current.insert(vertex);
        let neighbors = &adjacency[&vertex];
        bron_kerbosch(
            next_current,
            possible.intersection(neighbors).copied().collect(),
            excluded.intersection(neighbors).copied().collect(),
            adjacency,
            cliques,
            search_nodes,
        )?;
        possible.remove(&vertex);
        excluded.insert(vertex);
    }
    Ok(())
}

fn normalize_antichain(
    candidates: &mut BTreeSet<Vec<ContactOccurrenceId>>,
    confirmed: &BTreeSet<Vec<ContactOccurrenceId>>,
) {
    let snapshot = candidates.iter().cloned().collect::<Vec<_>>();
    candidates.retain(|candidate| {
        !confirmed
            .iter()
            .any(|support| is_subset(candidate, support))
            && !snapshot.iter().any(|other| {
                candidate != other && candidate.len() < other.len() && is_subset(candidate, other)
            })
    });
}

fn normalize_witness_candidates(
    candidates: &mut BTreeSet<Vec<ContactOccurrenceId>>,
    confirmed: &BTreeSet<Vec<ContactOccurrenceId>>,
) {
    candidates.retain(|candidate| {
        !confirmed
            .iter()
            .any(|support| is_subset(candidate, support) || is_subset(support, candidate))
    });
}

fn private_witness_obstruction(
    receiver: DivisorReceiverId,
    chronology: &[ContactOccurrenceId],
    pair_responses: &BTreeMap<Vec<ContactOccurrenceId>, bool>,
    confirmed: &BTreeSet<Vec<ContactOccurrenceId>>,
) -> Option<PrivateGeneratorWitnessObstruction> {
    let uncovered_occurrences = chronology
        .iter()
        .filter(|occurrence| {
            !confirmed
                .iter()
                .any(|support| support.binary_search(occurrence).is_ok())
        })
        .copied()
        .collect::<Vec<_>>();
    let uncovered_positive_pairs = pair_responses
        .iter()
        .filter(|(pair, response)| {
            **response && !confirmed.iter().any(|support| is_subset(pair, support))
        })
        .map(|(pair, _)| pair.clone())
        .collect::<Vec<_>>();
    if uncovered_occurrences.is_empty() && uncovered_positive_pairs.is_empty() {
        None
    } else {
        Some(PrivateGeneratorWitnessObstruction {
            schema: "holonic-engine.private-generator-witness-obstruction.v1".to_owned(),
            receiver,
            uncovered_occurrences,
            uncovered_positive_pairs,
        })
    }
}

fn next_facet_candidate(
    candidates: &BTreeSet<Vec<ContactOccurrenceId>>,
) -> Option<Vec<ContactOccurrenceId>> {
    candidates
        .iter()
        .min_by(|left, right| right.len().cmp(&left.len()).then_with(|| left.cmp(right)))
        .cloned()
}

fn is_subset<T: Ord>(subset: &[T], superset: &[T]) -> bool {
    let mut lower = 0;
    let mut upper = 0;
    while lower < subset.len() && upper < superset.len() {
        match subset[lower].cmp(&superset[upper]) {
            std::cmp::Ordering::Less => return false,
            std::cmp::Ordering::Equal => {
                lower += 1;
                upper += 1;
            }
            std::cmp::Ordering::Greater => upper += 1,
        }
    }
    lower == subset.len()
}

fn build_certificate(
    receiver: DivisorReceiverId,
    chronology: &[ContactOccurrenceId],
    mut supports: Vec<Vec<ContactOccurrenceId>>,
) -> Result<DivisorReconstructionCertificate, DivisorReconstructionError> {
    supports.sort();
    supports.dedup();
    if supports.is_empty() {
        return Err(DivisorReconstructionError::UncoveredOccurrence);
    }
    let generator_supports = supports
        .iter()
        .enumerate()
        .map(|(index, occurrences)| {
            Ok(LatentGeneratorSupport {
                generator: LatentGeneratorId(
                    u64::try_from(index)
                        .map_err(|_| DivisorReconstructionError::CarrierOverflow)?,
                ),
                occurrences: occurrences.clone(),
            })
        })
        .collect::<Result<Vec<_>, DivisorReconstructionError>>()?;
    let mut occurrence_memberships = chronology
        .iter()
        .map(|occurrence| (*occurrence, Vec::new()))
        .collect::<BTreeMap<_, _>>();
    for support in &generator_supports {
        for occurrence in &support.occurrences {
            occurrence_memberships
                .get_mut(occurrence)
                .ok_or(DivisorReconstructionError::MalformedCertificate)?
                .push(support.generator);
        }
    }
    if occurrence_memberships
        .values()
        .any(|memberships| memberships.is_empty())
    {
        return Err(DivisorReconstructionError::UncoveredOccurrence);
    }

    let mut cell_witnesses = BTreeMap::<Vec<LatentGeneratorId>, Vec<ContactOccurrenceId>>::new();
    for (occurrence, memberships) in &occurrence_memberships {
        for size in 1..=memberships.len() {
            for generators in combinations(memberships, size) {
                cell_witnesses
                    .entry(generators)
                    .or_default()
                    .push(*occurrence);
            }
        }
    }
    let generator_cells = cell_witnesses
        .into_iter()
        .map(|(generators, witness_occurrences)| {
            let grade = u32::try_from(generators.len() - 1)
                .map_err(|_| DivisorReconstructionError::CarrierOverflow)?;
            let boundary = if generators.len() == 1 {
                Vec::new()
            } else {
                (0..generators.len())
                    .map(|removed| {
                        let mut face = generators.clone();
                        face.remove(removed);
                        ReconstructedBoundaryTerm {
                            generators: face,
                            hand: if removed % 2 == 0 { 1 } else { -1 },
                        }
                    })
                    .collect()
            };
            Ok(ReconstructedGeneratorCell {
                generators,
                grade,
                witness_occurrences,
                boundary,
            })
        })
        .collect::<Result<Vec<_>, DivisorReconstructionError>>()?;
    let support_memberships = generator_supports.iter().try_fold(0_u64, |sum, support| {
        sum.checked_add(
            u64::try_from(support.occurrences.len())
                .map_err(|_| DivisorReconstructionError::CarrierOverflow)?,
        )
        .ok_or(DivisorReconstructionError::CarrierOverflow)
    })?;
    let mut positive_pairs = BTreeSet::new();
    for support in &supports {
        for pair in combinations(support, 2) {
            positive_pairs.insert(pair);
        }
    }
    let certificate = DivisorReconstructionCertificate {
        schema: "holonic-engine.divisor-reconstruction-certificate.v1".to_owned(),
        receiver,
        chronology: chronology.to_vec(),
        generator_supports,
        occurrence_memberships,
        generator_cells,
        compression: LatentContactCompression {
            occurrence_count: u64::try_from(chronology.len())
                .map_err(|_| DivisorReconstructionError::CarrierOverflow)?,
            latent_generator_count: u64::try_from(supports.len())
                .map_err(|_| DivisorReconstructionError::CarrierOverflow)?,
            support_memberships,
            expanded_positive_pair_contacts: u64::try_from(positive_pairs.len())
                .map_err(|_| DivisorReconstructionError::CarrierOverflow)?,
            all_pair_slots: pair_slot_count(chronology.len())?,
        },
    };
    Ok(certificate)
}

fn combinations<T: Clone>(population: &[T], size: usize) -> Vec<Vec<T>> {
    fn visit<T: Clone>(
        population: &[T],
        remaining: usize,
        next: usize,
        prefix: &mut Vec<T>,
        result: &mut Vec<Vec<T>>,
    ) {
        if remaining == 0 {
            result.push(prefix.clone());
            return;
        }
        let final_start = population.len().saturating_sub(remaining);
        for member in next..=final_start {
            prefix.push(population[member].clone());
            visit(population, remaining - 1, member + 1, prefix, result);
            prefix.pop();
        }
    }
    if size > population.len() {
        return Vec::new();
    }
    let mut result = Vec::new();
    visit(
        population,
        size,
        0,
        &mut Vec::with_capacity(size),
        &mut result,
    );
    result
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum DivisorReconstructionEvent {
    FoundOccurrenceReceiver {
        event: EventId,
        receiver: DivisorReceiverId,
        chronology: Vec<ContactOccurrenceId>,
    },
    ReturnContact {
        event: EventId,
        receiver: DivisorReceiverId,
        query: DivisorContactQuery,
        common_generator: bool,
    },
}

impl DivisorReconstructionEvent {
    fn event(&self) -> EventId {
        match self {
            Self::FoundOccurrenceReceiver { event, .. } | Self::ReturnContact { event, .. } => {
                *event
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DivisorReconstructionRadiation {
    pub schema: String,
    pub event: EventId,
    pub founded_receiver: Option<DivisorReceiverId>,
    pub received_testimony: Option<DivisorContactTestimony>,
    pub version_fiber: DivisorContactVersionFiber,
    pub next_query: Option<DivisorContactQuery>,
    pub certificate: Option<DivisorReconstructionCertificate>,
    pub obstruction: Option<PrivateGeneratorWitnessObstruction>,
    pub work: DivisorReconstructionWork,
}

#[derive(Clone, Copy, Debug)]
pub struct DivisorReconstructionLaw {
    doctrine: DivisorReconstructionDoctrine,
}

impl Default for DivisorReconstructionLaw {
    fn default() -> Self {
        Self::new(DivisorReconstructionDoctrine::CompleteContactComplex)
    }
}

impl DivisorReconstructionLaw {
    pub const fn new(doctrine: DivisorReconstructionDoctrine) -> Self {
        Self { doctrine }
    }

    pub const fn doctrine(self) -> DivisorReconstructionDoctrine {
        self.doctrine
    }
}

impl ExactEventLaw for DivisorReconstructionLaw {
    type Standing = DivisorReconstructionStanding;
    type Event = DivisorReconstructionEvent;
    type Radiation = DivisorReconstructionRadiation;
    type Error = DivisorReconstructionError;

    fn enact(
        &self,
        standing_before: &Self::Standing,
        event: &Self::Event,
    ) -> Result<EventSuccessor<Self::Standing, Self::Radiation>, Self::Error> {
        // The law receives only successors it previously formed.  The
        // incremental validator checks the complete carried recurrence and
        // query frontier without replaying every already-returned pair.
        // `DivisorReconstructionStanding::validate` remains the independent
        // full-history authority used at grading and persistence boundaries.
        standing_before.validate_incremental()?;
        if standing_before
            .doctrine
            .is_some_and(|doctrine| doctrine != self.doctrine)
        {
            return Err(DivisorReconstructionError::LawStandingMismatch);
        }
        let event_id = event.event();
        if standing_before.used_events.contains(&event_id) {
            return Err(DivisorReconstructionError::RepeatedEvent(event_id));
        }
        let mut standing_after = standing_before.clone();
        let mut founded_receiver = None;
        let mut received_testimony = None;
        match event {
            DivisorReconstructionEvent::FoundOccurrenceReceiver {
                event,
                receiver,
                chronology,
            } => {
                standing_after.apply_founding(
                    *event,
                    *receiver,
                    self.doctrine,
                    chronology.clone(),
                )?;
                founded_receiver = Some(*receiver);
            }
            DivisorReconstructionEvent::ReturnContact {
                event,
                receiver,
                query,
                common_generator,
            } => {
                if query.receiver != *receiver {
                    return Err(DivisorReconstructionError::ReceiverMismatch {
                        expected: query.receiver,
                        received: *receiver,
                    });
                }
                let testimony = DivisorContactTestimony {
                    event: *event,
                    query: query.clone(),
                    common_generator: *common_generator,
                };
                standing_after.apply_testimony(testimony.clone())?;
                received_testimony = Some(testimony);
            }
        }
        standing_after.validate_incremental()?;
        let work = standing_after
            .work
            .checked_difference(&standing_before.work)?;
        let radiation = DivisorReconstructionRadiation {
            schema: "holonic-engine.divisor-reconstruction-radiation.v1".to_owned(),
            event: event_id,
            founded_receiver,
            received_testimony,
            version_fiber: standing_after
                .version_fiber
                .clone()
                .ok_or(DivisorReconstructionError::MalformedStanding)?,
            next_query: standing_after.next_query.clone(),
            certificate: standing_after.certificate.clone(),
            obstruction: standing_after.obstruction.clone(),
            work,
        };
        Ok(EventSuccessor {
            standing_after,
            radiation: vec![radiation],
            logical_resources: None,
            physical_resources: None,
        })
    }
}

/// Grading-only correspondence between an unlabeled reconstructed generator
/// and the arithmetic authority's prime axis.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GradedGeneratorCorrespondence {
    pub latent_generator: LatentGeneratorId,
    pub grading_prime: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArithmeticDivisorReconstructionGrade {
    pub schema: String,
    pub receiver: DivisorReceiverId,
    pub support_ecology_exact: bool,
    pub generator_complex_exact: bool,
    pub generator_boundary_squared_zero: bool,
    pub correspondence: Vec<GradedGeneratorCorrespondence>,
    pub explicit_contact_returns: u64,
    pub explicit_higher_order_returns: u64,
    pub heldout_contact_sections: u64,
    pub heldout_false_positives: u64,
    pub heldout_false_negatives: u64,
    pub latent_support_memberships: u64,
    pub expanded_positive_pair_contacts: u64,
}

impl ArithmeticDivisorReconstructionGrade {
    pub fn is_exact(&self) -> bool {
        self.support_ecology_exact
            && self.generator_complex_exact
            && self.generator_boundary_squared_zero
            && self.heldout_false_positives == 0
            && self.heldout_false_negatives == 0
    }
}

/// The arithmetic authority behind a black-box contact membrane.
///
/// This type is intentionally not part of `DivisorReconstructionStanding`.
/// It alone knows the map from opaque chronology ordinals to integer
/// occurrences and uses retained valuations to answer returned contact.
pub struct ArithmeticDivisorMembrane<'a> {
    arithmetic: &'a ArithmeticFiberStanding,
    receiver: DivisorReceiverId,
    chronology: Vec<ContactOccurrenceId>,
    occurrence_values: BTreeMap<ContactOccurrenceId, u64>,
}

impl<'a> ArithmeticDivisorMembrane<'a> {
    pub fn new(
        arithmetic: &'a ArithmeticFiberStanding,
        receiver: DivisorReceiverId,
    ) -> Result<Self, DivisorReconstructionError> {
        arithmetic.validate()?;
        if arithmetic.occurrences().is_empty() {
            return Err(DivisorReconstructionError::EmptyArithmeticMembrane);
        }
        let mut chronology = Vec::with_capacity(arithmetic.occurrences().len());
        let mut occurrence_values = BTreeMap::new();
        for (index, value) in arithmetic.occurrences().keys().copied().enumerate() {
            let occurrence = ContactOccurrenceId(
                u64::try_from(index).map_err(|_| DivisorReconstructionError::CarrierOverflow)?,
            );
            chronology.push(occurrence);
            occurrence_values.insert(occurrence, value);
        }
        Ok(Self {
            arithmetic,
            receiver,
            chronology,
            occurrence_values,
        })
    }

    pub fn receiver(&self) -> DivisorReceiverId {
        self.receiver
    }

    pub fn chronology(&self) -> &[ContactOccurrenceId] {
        &self.chronology
    }

    pub fn occurrence_value(&self, occurrence: ContactOccurrenceId) -> Option<u64> {
        self.occurrence_values.get(&occurrence).copied()
    }

    pub fn answer(&self, query: &DivisorContactQuery) -> Result<bool, DivisorReconstructionError> {
        query.validate()?;
        if query.receiver != self.receiver {
            return Err(DivisorReconstructionError::ReceiverMismatch {
                expected: self.receiver,
                received: query.receiver,
            });
        }
        self.common_generator(&query.members)
    }

    pub fn returned_event(
        &self,
        event: EventId,
        query: DivisorContactQuery,
    ) -> Result<DivisorReconstructionEvent, DivisorReconstructionError> {
        let common_generator = self.answer(&query)?;
        Ok(DivisorReconstructionEvent::ReturnContact {
            event,
            receiver: self.receiver,
            query,
            common_generator,
        })
    }

    pub fn grade(
        &self,
        reconstruction: &DivisorReconstructionStanding,
        maximum_heldout_order: usize,
    ) -> Result<ArithmeticDivisorReconstructionGrade, DivisorReconstructionError> {
        reconstruction.validate()?;
        if reconstruction.receiver != Some(self.receiver)
            || reconstruction.chronology != self.chronology
        {
            return Err(DivisorReconstructionError::GradingReceiverMismatch);
        }
        let certificate = reconstruction
            .certificate()
            .ok_or(DivisorReconstructionError::ReconstructionStillOpen)?;
        let mut expected_supports = BTreeMap::<u64, Vec<ContactOccurrenceId>>::new();
        for prime in self.arithmetic.prime_cells().keys() {
            expected_supports.insert(*prime, Vec::new());
        }
        for (occurrence, value) in &self.occurrence_values {
            let received = &self.arithmetic.occurrences()[value];
            for valuation in &received.valuation {
                expected_supports
                    .get_mut(&valuation.prime)
                    .ok_or(DivisorReconstructionError::MalformedArithmeticMembrane)?
                    .push(*occurrence);
            }
        }
        let expected_set = expected_supports.values().cloned().collect::<BTreeSet<_>>();
        let received_set = certificate
            .generator_supports
            .iter()
            .map(|support| support.occurrences.clone())
            .collect::<BTreeSet<_>>();
        let support_ecology_exact = expected_set == received_set;
        let mut correspondence = Vec::new();
        if support_ecology_exact {
            for support in &certificate.generator_supports {
                let prime = expected_supports
                    .iter()
                    .find_map(|(prime, expected)| {
                        (expected == &support.occurrences).then_some(*prime)
                    })
                    .ok_or(DivisorReconstructionError::MalformedArithmeticMembrane)?;
                correspondence.push(GradedGeneratorCorrespondence {
                    latent_generator: support.generator,
                    grading_prime: prime,
                });
            }
        }
        let correspondence_map = correspondence
            .iter()
            .map(|entry| (entry.latent_generator, entry.grading_prime))
            .collect::<BTreeMap<_, _>>();
        let received_generator_cells = certificate
            .generator_cells
            .iter()
            .map(|cell| {
                let mut primes = cell
                    .generators
                    .iter()
                    .map(|generator| correspondence_map.get(generator).copied())
                    .collect::<Option<Vec<_>>>()
                    .unwrap_or_default();
                primes.sort_unstable();
                primes
            })
            .collect::<BTreeSet<_>>();
        let expected_generator_cells = self
            .arithmetic
            .squarefree_cells()
            .keys()
            .cloned()
            .collect::<BTreeSet<_>>();
        let generator_complex_exact =
            support_ecology_exact && received_generator_cells == expected_generator_cells;

        let explicit = reconstruction
            .history
            .iter()
            .map(|testimony| testimony.query.members.clone())
            .collect::<BTreeSet<_>>();
        let mut heldout_contact_sections = 0_u64;
        let mut heldout_false_positives = 0_u64;
        let mut heldout_false_negatives = 0_u64;
        for order in 2..=maximum_heldout_order.min(self.chronology.len()) {
            for section in combinations(&self.chronology, order) {
                if explicit.contains(&section) {
                    continue;
                }
                heldout_contact_sections = heldout_contact_sections
                    .checked_add(1)
                    .ok_or(DivisorReconstructionError::CarrierOverflow)?;
                let predicted = certificate.predicts_contact(&section)?;
                let actual = self.common_generator(&section)?;
                match (predicted, actual) {
                    (true, false) => {
                        heldout_false_positives = heldout_false_positives
                            .checked_add(1)
                            .ok_or(DivisorReconstructionError::CarrierOverflow)?;
                    }
                    (false, true) => {
                        heldout_false_negatives = heldout_false_negatives
                            .checked_add(1)
                            .ok_or(DivisorReconstructionError::CarrierOverflow)?;
                    }
                    _ => {}
                }
            }
        }
        Ok(ArithmeticDivisorReconstructionGrade {
            schema: "holonic-engine.arithmetic-divisor-reconstruction-grade.v1".to_owned(),
            receiver: self.receiver,
            support_ecology_exact,
            generator_complex_exact,
            generator_boundary_squared_zero: certificate.generator_boundary_squared_zero(),
            correspondence,
            explicit_contact_returns: u64::try_from(reconstruction.history.len())
                .map_err(|_| DivisorReconstructionError::CarrierOverflow)?,
            explicit_higher_order_returns: reconstruction.work.higher_order_returns,
            heldout_contact_sections,
            heldout_false_positives,
            heldout_false_negatives,
            latent_support_memberships: certificate.compression.support_memberships,
            expanded_positive_pair_contacts: certificate
                .compression
                .expanded_positive_pair_contacts,
        })
    }

    fn common_generator(
        &self,
        members: &[ContactOccurrenceId],
    ) -> Result<bool, DivisorReconstructionError> {
        if members.is_empty() || members.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(DivisorReconstructionError::MalformedContactSection(
                members.to_vec(),
            ));
        }
        let mut common = None::<BTreeSet<u64>>;
        for member in members {
            let value = self.occurrence_values.get(member).copied().ok_or_else(|| {
                DivisorReconstructionError::MalformedContactSection(members.to_vec())
            })?;
            let support = self.arithmetic.occurrences()[&value]
                .squarefree_support
                .iter()
                .copied()
                .collect::<BTreeSet<_>>();
            match &mut common {
                Some(common) => common.retain(|prime| support.contains(prime)),
                None => common = Some(support),
            }
            if common.as_ref().is_some_and(BTreeSet::is_empty) {
                return Ok(false);
            }
        }
        Ok(common.is_some_and(|common| !common.is_empty()))
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum DivisorReconstructionError {
    #[error("the divisor-reconstruction law and standing doctrines disagree")]
    LawStandingMismatch,
    #[error("the occurrence receiver is already founded")]
    ReceiverAlreadyFounded,
    #[error("an occurrence receiver requires a nonempty strictly ordered chronology")]
    MalformedChronology,
    #[error("divisor reconstruction occurrence {0:?} was already used")]
    RepeatedEvent(EventId),
    #[error("divisor contact query {0:?} is malformed")]
    MalformedQuery(DivisorContactQuery),
    #[error("contact section {0:?} is malformed for this receiver")]
    MalformedContactSection(Vec<ContactOccurrenceId>),
    #[error("returned query {received:?} does not match production query {expected:?}")]
    UnexpectedReturnedQuery {
        expected: Option<DivisorContactQuery>,
        received: DivisorContactQuery,
    },
    #[error("receiver mismatch: expected {expected:?}, received {received:?}")]
    ReceiverMismatch {
        expected: DivisorReceiverId,
        received: DivisorReceiverId,
    },
    #[error("the same contact section returned more than once")]
    RepeatedContactSection,
    #[error("the reconstructed latent ecology leaves an occurrence uncovered")]
    UncoveredOccurrence,
    #[error("the divisor-reconstruction standing is malformed")]
    MalformedStanding,
    #[error("the divisor-reconstruction certificate is malformed")]
    MalformedCertificate,
    #[error("finite divisor reconstruction exceeded an exact carrier")]
    CarrierOverflow,
    #[error("an arithmetic contact membrane requires at least one arithmetic occurrence")]
    EmptyArithmeticMembrane,
    #[error("the arithmetic contact membrane is malformed")]
    MalformedArithmeticMembrane,
    #[error("the arithmetic grader and reconstructed receiver disagree")]
    GradingReceiverMismatch,
    #[error("the latent reconstruction is still open")]
    ReconstructionStillOpen,
    #[error(transparent)]
    Arithmetic(#[from] ArithmeticFiberError),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ArithmeticFiberEvent, ArithmeticFiberLaw, CausalWorld};

    fn arithmetic_through(limit: u64) -> ArithmeticFiberStanding {
        let mut world = CausalWorld::new(ArithmeticFiberLaw, ArithmeticFiberStanding::default());
        for value in 2..=limit {
            world
                .receive(&ArithmeticFiberEvent {
                    event: EventId(value - 1),
                    value,
                })
                .unwrap();
        }
        world.standing().clone()
    }

    fn reconstruct_arithmetic(
        arithmetic: &ArithmeticFiberStanding,
    ) -> (
        DivisorReconstructionStanding,
        ArithmeticDivisorReconstructionGrade,
    ) {
        let receiver = DivisorReceiverId(7);
        let membrane = ArithmeticDivisorMembrane::new(arithmetic, receiver).unwrap();
        let mut world = CausalWorld::new(
            DivisorReconstructionLaw::new(
                DivisorReconstructionDoctrine::PrivateWitnessedGeneratorFacets,
            ),
            DivisorReconstructionStanding::default(),
        );
        world
            .receive(&DivisorReconstructionEvent::FoundOccurrenceReceiver {
                event: EventId(10_000),
                receiver,
                chronology: membrane.chronology().to_vec(),
            })
            .unwrap();
        let mut event = 10_001_u64;
        while let Some(query) = world.standing().next_query().cloned() {
            world
                .receive(&membrane.returned_event(EventId(event), query).unwrap())
                .unwrap();
            event += 1;
        }
        let grade = membrane.grade(world.standing(), 4).unwrap();
        (world.standing().clone(), grade)
    }

    #[test]
    fn a_false_triangle_separates_into_three_latent_pair_facets() {
        let receiver = DivisorReceiverId(1);
        let chronology = vec![
            ContactOccurrenceId(10),
            ContactOccurrenceId(20),
            ContactOccurrenceId(30),
        ];
        let true_supports = [
            vec![chronology[0], chronology[1]],
            vec![chronology[0], chronology[2]],
            vec![chronology[1], chronology[2]],
        ];
        let mut world = CausalWorld::new(
            DivisorReconstructionLaw::default(),
            DivisorReconstructionStanding::default(),
        );
        world
            .receive(&DivisorReconstructionEvent::FoundOccurrenceReceiver {
                event: EventId(1),
                receiver,
                chronology: chronology.clone(),
            })
            .unwrap();
        let mut event = 2_u64;
        while let Some(query) = world.standing().next_query().cloned() {
            let common_generator = true_supports
                .iter()
                .any(|support| is_subset(&query.members, support));
            world
                .receive(&DivisorReconstructionEvent::ReturnContact {
                    event: EventId(event),
                    receiver,
                    query,
                    common_generator,
                })
                .unwrap();
            event += 1;
        }
        let standing = world.standing();
        let certificate = standing.certificate().unwrap();
        assert_eq!(standing.work.pairwise_returns, 3);
        assert_eq!(standing.work.higher_order_returns, 1);
        assert_eq!(standing.work.negative_candidate_splits, 1);
        assert_eq!(
            certificate
                .generator_supports
                .iter()
                .map(|support| support.occurrences.clone())
                .collect::<BTreeSet<_>>(),
            true_supports.into_iter().collect()
        );
        assert_eq!(
            certificate.generator_f_vector(),
            BTreeMap::from([(0, 3), (1, 3)])
        );
        standing.validate().unwrap();
    }

    #[test]
    fn a_false_triangle_obstructs_a_private_witness_doctrine() {
        let receiver = DivisorReceiverId(2);
        let chronology = vec![
            ContactOccurrenceId(10),
            ContactOccurrenceId(20),
            ContactOccurrenceId(30),
        ];
        let true_supports = [
            vec![chronology[0], chronology[1]],
            vec![chronology[0], chronology[2]],
            vec![chronology[1], chronology[2]],
        ];
        let mut world = CausalWorld::new(
            DivisorReconstructionLaw::new(
                DivisorReconstructionDoctrine::PrivateWitnessedGeneratorFacets,
            ),
            DivisorReconstructionStanding::default(),
        );
        world
            .receive(&DivisorReconstructionEvent::FoundOccurrenceReceiver {
                event: EventId(1),
                receiver,
                chronology: chronology.clone(),
            })
            .unwrap();
        let mut event = 2_u64;
        while let Some(query) = world.standing().next_query().cloned() {
            let common_generator = true_supports
                .iter()
                .any(|support| is_subset(&query.members, support));
            world
                .receive(&DivisorReconstructionEvent::ReturnContact {
                    event: EventId(event),
                    receiver,
                    query,
                    common_generator,
                })
                .unwrap();
            event += 1;
        }
        let standing = world.standing();
        assert!(standing.certificate().is_none());
        let obstruction = standing.obstruction().unwrap();
        assert_eq!(obstruction.uncovered_occurrences, chronology);
        assert_eq!(
            obstruction.uncovered_positive_pairs,
            true_supports.into_iter().collect::<Vec<_>>()
        );
        assert!(standing.version_fiber().unwrap().doctrine_obstructed);
        standing.validate().unwrap();
    }

    #[test]
    fn arithmetic_contact_reconstructs_unlabeled_prime_support_and_dual_cells() {
        let arithmetic = arithmetic_through(30);
        let (standing, grade) = reconstruct_arithmetic(&arithmetic);
        assert!(grade.is_exact());
        assert_eq!(grade.correspondence.len(), 10);
        assert!(grade.heldout_contact_sections > 0);
        assert_eq!(grade.heldout_false_positives, 0);
        assert_eq!(grade.heldout_false_negatives, 0);
        assert_eq!(
            standing.certificate().unwrap().generator_f_vector(),
            BTreeMap::from([(0, 10), (1, 7), (2, 1)])
        );
        assert!(
            standing
                .certificate()
                .unwrap()
                .generator_boundary_squared_zero()
        );
        assert_eq!(standing.work.higher_order_returns, 4);
        assert_eq!(standing.work.negative_candidate_splits, 0);
        assert_eq!(standing.work.rejected_witness_candidates, 0);
        assert!(grade.expanded_positive_pair_contacts > grade.latent_support_memberships);
        standing.validate().unwrap();
    }

    #[test]
    fn production_sees_only_receiver_ordinals_and_owns_every_query() {
        let arithmetic = arithmetic_through(15);
        let receiver = DivisorReceiverId(3);
        let membrane = ArithmeticDivisorMembrane::new(&arithmetic, receiver).unwrap();
        assert_eq!(
            membrane.chronology(),
            &(0..14).map(ContactOccurrenceId).collect::<Vec<_>>()
        );
        assert_eq!(membrane.occurrence_value(ContactOccurrenceId(0)), Some(2));
        assert_eq!(membrane.occurrence_value(ContactOccurrenceId(13)), Some(15));

        let mut world = CausalWorld::new(
            DivisorReconstructionLaw::default(),
            DivisorReconstructionStanding::default(),
        );
        world
            .receive(&DivisorReconstructionEvent::FoundOccurrenceReceiver {
                event: EventId(100),
                receiver,
                chronology: membrane.chronology().to_vec(),
            })
            .unwrap();
        let expected = world.standing().next_query().cloned().unwrap();
        let mut wrong = expected.clone();
        wrong.members = vec![ContactOccurrenceId(0), ContactOccurrenceId(2)];
        let before = world.standing().clone();
        assert!(matches!(
            world.receive(&DivisorReconstructionEvent::ReturnContact {
                event: EventId(101),
                receiver,
                query: wrong,
                common_generator: false,
            }),
            Err(DivisorReconstructionError::UnexpectedReturnedQuery { .. })
        ));
        assert_eq!(world.standing(), &before);
        world
            .receive(&membrane.returned_event(EventId(101), expected).unwrap())
            .unwrap();
    }

    #[test]
    fn altered_fiber_or_certificate_cannot_become_standing() {
        let arithmetic = arithmetic_through(20);
        let (standing, _) = reconstruct_arithmetic(&arithmetic);
        let mut forged_fiber = standing.clone();
        forged_fiber
            .version_fiber
            .as_mut()
            .unwrap()
            .positive_sections
            .clear();
        assert_eq!(
            forged_fiber.validate(),
            Err(DivisorReconstructionError::MalformedStanding)
        );

        let mut forged_certificate = standing;
        forged_certificate
            .certificate
            .as_mut()
            .unwrap()
            .generator_supports[0]
            .occurrences
            .pop();
        assert!(matches!(
            forged_certificate.validate(),
            Err(DivisorReconstructionError::MalformedCertificate)
                | Err(DivisorReconstructionError::MalformedStanding)
        ));
    }
}
