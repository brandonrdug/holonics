//! Exact population current through a receiver-caused passage ecology.
//!
//! This is the shared discrete transport protocol for identities whose carried
//! current is an exact population rather than a rational coordinate vector.
//! A passage has positive characteristic delay.  At each reached site the
//! complete co-present branch demand meets the site's retained capacity; the
//! required service rounds dilate every participating branch together.  No
//! branch is selected by a score, ranking, or lexical preference.
//!
//! Equal-arrival currents superpose as exact populations while retaining the
//! complete predecessor incidence.  Later arrivals remain explicit deferred
//! testimony.  The factorized predecessor body can be observed without
//! pretending its union was one enacted path: witness paths remain separate.

use holonic_structure::{LocalQueue, LocalRelations, LocalSequence, LocalSet, SparseOrdinalAtlas};
use num_bigint::BigUint;
use num_traits::{One, ToPrimitive, Zero};
use thiserror::Error;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ReceiverCurrentSiteId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ReceiverCurrentPassageId(pub u64);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactReceiverCurrentSite {
    pub id: ReceiverCurrentSiteId,
    /// Exact co-present current population which can be served in one round.
    pub capacity: BigUint,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactReceiverCurrentPassage {
    pub id: ReceiverCurrentPassageId,
    pub from: ReceiverCurrentSiteId,
    pub to: ReceiverCurrentSiteId,
    /// Positive receiver chronology required by an otherwise uncongested
    /// passage.
    pub characteristic_delay: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ExactReceiverCurrentPredecessor {
    pub from: ReceiverCurrentSiteId,
    pub passage: ReceiverCurrentPassageId,
    pub departure_chronology: u64,
    pub passage_delay: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactReceiverCurrentArrival {
    pub site: ReceiverCurrentSiteId,
    pub chronology: u64,
    pub population: BigUint,
    pub predecessors: LocalSet<ExactReceiverCurrentPredecessor>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactReceiverCurrentPassageReceipt {
    pub passage: ReceiverCurrentPassageId,
    pub from: ReceiverCurrentSiteId,
    pub to: ReceiverCurrentSiteId,
    pub departure_chronology: u64,
    pub characteristic_delay: u64,
    pub branch_population: BigUint,
    pub co_present_branch_population: BigUint,
    pub site_capacity: BigUint,
    pub service_rounds: BigUint,
    pub passage_delay: u64,
    pub arrival_chronology: u64,
}

/// A later arrival which cannot overwrite the receiver's already-caused
/// earliest section.  It remains available to a later horizon or recurrent
/// event instead of being discarded as a failed shortest path.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ExactReceiverCurrentDeferredArrival {
    pub site: ReceiverCurrentSiteId,
    pub chronology: u64,
    pub population: BigUint,
    pub predecessors: LocalSet<ExactReceiverCurrentPredecessor>,
}

/// One enacted predecessor path.  This is an inspection membrane over the
/// factorized arrival DAG, not the primary representation of path population.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ExactReceiverCurrentWitness {
    pub sites: Vec<ReceiverCurrentSiteId>,
    pub passages: Vec<ReceiverCurrentPassageId>,
    pub arrival_chronology: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactReceiverCurrentRadiation {
    pub sources: LocalSet<ReceiverCurrentSiteId>,
    pub requested_targets: LocalSet<ReceiverCurrentSiteId>,
    pub returned_targets: LocalSet<ReceiverCurrentSiteId>,
    pub receiver_horizon: Option<u64>,
    pub arrivals: ExactReceiverCurrentArrivalAtlas,
    pub passage_receipts: Vec<ExactReceiverCurrentPassageReceipt>,
    pub deferred_arrivals: LocalSet<ExactReceiverCurrentDeferredArrival>,
}

/// Sparse receiver-addressed arrival population. The physical page directory is owned by
/// `holonic-structure`; a language or physics application can observe receiver identities but
/// cannot acquire or reinterpret the directory as its own graph.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ExactReceiverCurrentArrivalAtlas {
    standing: SparseOrdinalAtlas<ExactReceiverCurrentArrival>,
}

impl ExactReceiverCurrentArrivalAtlas {
    pub fn get(&self, site: &ReceiverCurrentSiteId) -> Option<&ExactReceiverCurrentArrival> {
        self.standing.get(site.0)
    }

    fn get_mut(&mut self, site: ReceiverCurrentSiteId) -> Option<&mut ExactReceiverCurrentArrival> {
        self.standing.get_mut(site.0)
    }

    fn found(
        &mut self,
        arrival: ExactReceiverCurrentArrival,
    ) -> Result<(), ExactReceiverCurrentError> {
        self.standing
            .try_found(arrival.site.0, arrival)
            .map_err(|_| ExactReceiverCurrentError::CarrierExtent)
    }

    pub fn keys(&self) -> impl Iterator<Item = &ReceiverCurrentSiteId> {
        self.standing.values().map(|arrival| &arrival.site)
    }
}

impl ExactReceiverCurrentRadiation {
    pub fn exact_path_population(&self, target: ReceiverCurrentSiteId) -> BigUint {
        match self.arrivals.get(&target) {
            Some(arrival) => arrival.population.clone(),
            None => BigUint::zero(),
        }
    }

    /// Restrict the factorized predecessor body to one exact receiver section.
    ///
    /// `receiver_phase` is an ordinal in the target's exact path population.  It is reduced
    /// through that population and then transported backwards through predecessor populations;
    /// no witness preceding it is enumerated and the retained radiation is not changed.  This is
    /// therefore a local observation chart over the complete DAG, not a canonical path promoted
    /// into standing.
    pub fn witness_section_to(
        &self,
        target: ReceiverCurrentSiteId,
        receiver_phase: &BigUint,
    ) -> Result<ExactReceiverCurrentWitness, ExactReceiverCurrentError> {
        let target_arrival = self
            .arrivals
            .get(&target)
            .ok_or(ExactReceiverCurrentError::UnreturnedTarget(target))?;
        if !self.returned_targets.contains(&target) || target_arrival.population.is_zero() {
            return Err(ExactReceiverCurrentError::UnreturnedTarget(target));
        }

        let target_chronology = target_arrival.chronology;
        let mut phase = receiver_phase % &target_arrival.population;
        let mut reverse_sites = LocalSequence::from([target]);
        let mut reverse_passages = LocalSequence::new();
        let mut at = target;
        while !self.sources.contains(&at) {
            let arrival = self
                .arrivals
                .get(&at)
                .ok_or(ExactReceiverCurrentError::MalformedRadiation)?;
            let mut selected = None;
            for predecessor in &arrival.predecessors {
                let prior = self
                    .arrivals
                    .get(&predecessor.from)
                    .ok_or(ExactReceiverCurrentError::MalformedRadiation)?;
                if prior.chronology >= arrival.chronology
                    || prior.chronology.checked_add(predecessor.passage_delay)
                        != Some(arrival.chronology)
                {
                    return Err(ExactReceiverCurrentError::MalformedRadiation);
                }
                if phase < prior.population {
                    selected = Some(predecessor);
                    break;
                }
                phase -= &prior.population;
            }
            let predecessor = selected.ok_or(ExactReceiverCurrentError::MalformedRadiation)?;
            reverse_passages.push(predecessor.passage);
            reverse_sites.push(predecessor.from);
            at = predecessor.from;
        }
        if !phase.is_zero() {
            return Err(ExactReceiverCurrentError::MalformedRadiation);
        }
        reverse_sites.reverse();
        reverse_passages.reverse();
        Ok(ExactReceiverCurrentWitness {
            sites: reverse_sites.into_inner(),
            passages: reverse_passages.into_inner(),
            arrival_chronology: target_chronology,
        })
    }

    /// Materialize the distinct minimal-arrival witnesses retained by the
    /// predecessor DAG.  The exact population in [`Self::arrivals`] remains
    /// authoritative when this inspection would exceed host address space.
    pub fn witness_paths_to(
        &self,
        target: ReceiverCurrentSiteId,
    ) -> Result<Vec<ExactReceiverCurrentWitness>, ExactReceiverCurrentError> {
        let arrival = self
            .arrivals
            .get(&target)
            .ok_or(ExactReceiverCurrentError::UnreturnedTarget(target))?;
        if !self.returned_targets.contains(&target) {
            return Err(ExactReceiverCurrentError::UnreturnedTarget(target));
        }
        let expected = arrival
            .population
            .to_usize()
            .ok_or(ExactReceiverCurrentError::CarrierExtent)?;
        let mut witnesses = Vec::with_capacity(expected);
        let mut reverse_sites = vec![target];
        let mut reverse_passages = Vec::new();
        self.extend_witnesses(
            target,
            arrival.chronology,
            &mut reverse_sites,
            &mut reverse_passages,
            &mut witnesses,
        )?;
        if witnesses.len() != expected {
            return Err(ExactReceiverCurrentError::MalformedRadiation);
        }
        witnesses.sort();
        Ok(witnesses)
    }

    fn extend_witnesses(
        &self,
        at: ReceiverCurrentSiteId,
        target_chronology: u64,
        reverse_sites: &mut Vec<ReceiverCurrentSiteId>,
        reverse_passages: &mut Vec<ReceiverCurrentPassageId>,
        witnesses: &mut Vec<ExactReceiverCurrentWitness>,
    ) -> Result<(), ExactReceiverCurrentError> {
        if self.sources.contains(&at) {
            let mut sites = reverse_sites.clone();
            sites.reverse();
            let mut passages = reverse_passages.clone();
            passages.reverse();
            witnesses.push(ExactReceiverCurrentWitness {
                sites,
                passages,
                arrival_chronology: target_chronology,
            });
            return Ok(());
        }
        let arrival = self
            .arrivals
            .get(&at)
            .ok_or(ExactReceiverCurrentError::MalformedRadiation)?;
        if arrival.predecessors.is_empty() {
            return Err(ExactReceiverCurrentError::MalformedRadiation);
        }
        for predecessor in &arrival.predecessors {
            let prior = self
                .arrivals
                .get(&predecessor.from)
                .ok_or(ExactReceiverCurrentError::MalformedRadiation)?;
            if prior.chronology >= arrival.chronology
                || prior.chronology.checked_add(predecessor.passage_delay)
                    != Some(arrival.chronology)
            {
                return Err(ExactReceiverCurrentError::MalformedRadiation);
            }
            reverse_sites.push(predecessor.from);
            reverse_passages.push(predecessor.passage);
            self.extend_witnesses(
                predecessor.from,
                target_chronology,
                reverse_sites,
                reverse_passages,
                witnesses,
            )?;
            reverse_passages.pop();
            reverse_sites.pop();
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum ExactReceiverCurrentError {
    #[error("receiver-current site {0:?} is already founded")]
    DuplicateSite(ReceiverCurrentSiteId),
    #[error("receiver-current passage {0:?} is already founded")]
    DuplicatePassage(ReceiverCurrentPassageId),
    #[error("receiver-current site {0:?} is unknown")]
    UnknownSite(ReceiverCurrentSiteId),
    #[error("receiver-current site {0:?} has zero capacity")]
    ZeroCapacity(ReceiverCurrentSiteId),
    #[error("receiver-current passage {0:?} has zero characteristic delay")]
    ZeroDelay(ReceiverCurrentPassageId),
    #[error("receiver-current radiation requires at least one source and one target")]
    EmptyRadiationBoundary,
    #[error("receiver-current target {0:?} did not return at this horizon")]
    UnreturnedTarget(ReceiverCurrentSiteId),
    #[error("receiver-current carrier extent exceeds the exact host address")]
    CarrierExtent,
    #[error("receiver-current radiation is internally inconsistent")]
    MalformedRadiation,
}

/// Incremental exact passage ecology.  Sites and passages are founded once;
/// returned recurrence may change a site's capacity without changing its
/// identity or rewriting prior passage testimony.
#[derive(Debug, PartialEq, Eq)]
pub struct ExactReceiverCurrentLaw {
    sites: SparseOrdinalAtlas<ExactReceiverCurrentSiteStanding>,
    passages: SparseOrdinalAtlas<ExactReceiverCurrentPassage>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ExactReceiverCurrentSiteStanding {
    site: ExactReceiverCurrentSite,
    outgoing: LocalSet<ReceiverCurrentPassageId>,
    incoming: LocalSet<ReceiverCurrentPassageId>,
}

impl Default for ExactReceiverCurrentLaw {
    fn default() -> Self {
        Self::new()
    }
}

impl ExactReceiverCurrentLaw {
    pub const fn new() -> Self {
        Self {
            sites: SparseOrdinalAtlas::new(),
            passages: SparseOrdinalAtlas::new(),
        }
    }

    pub fn sites(&self) -> impl Iterator<Item = &ExactReceiverCurrentSite> {
        self.sites.values().map(|standing| &standing.site)
    }

    pub fn site(&self, id: ReceiverCurrentSiteId) -> Option<&ExactReceiverCurrentSite> {
        Some(&self.sites.get(id.0)?.site)
    }

    pub fn passages(&self) -> impl Iterator<Item = &ExactReceiverCurrentPassage> {
        self.passages.values()
    }

    /// Return one already-founded passage by its causal identity.
    ///
    /// A surrounding ecology uses this receiver-local aperture to resume a compound passage
    /// return without replaying a direction which crossed before a later direction was refused.
    pub fn passage(&self, id: ReceiverCurrentPassageId) -> Option<&ExactReceiverCurrentPassage> {
        self.passages.get(id.0)
    }

    pub fn found_site(
        &mut self,
        id: ReceiverCurrentSiteId,
        capacity: BigUint,
    ) -> Result<(), ExactReceiverCurrentError> {
        if capacity.is_zero() {
            return Err(ExactReceiverCurrentError::ZeroCapacity(id));
        }
        if self.sites.contains(id.0) {
            return Err(ExactReceiverCurrentError::DuplicateSite(id));
        }
        self.sites
            .try_found(
                id.0,
                ExactReceiverCurrentSiteStanding {
                    site: ExactReceiverCurrentSite { id, capacity },
                    outgoing: LocalSet::new(),
                    incoming: LocalSet::new(),
                },
            )
            .map_err(|_| ExactReceiverCurrentError::CarrierExtent)
    }

    pub fn set_site_capacity(
        &mut self,
        id: ReceiverCurrentSiteId,
        capacity: BigUint,
    ) -> Result<(), ExactReceiverCurrentError> {
        if capacity.is_zero() {
            return Err(ExactReceiverCurrentError::ZeroCapacity(id));
        }
        self.sites
            .get_mut(id.0)
            .ok_or(ExactReceiverCurrentError::UnknownSite(id))?
            .site
            .capacity = capacity;
        Ok(())
    }

    pub fn found_passage(
        &mut self,
        passage: ExactReceiverCurrentPassage,
    ) -> Result<(), ExactReceiverCurrentError> {
        if passage.characteristic_delay == 0 {
            return Err(ExactReceiverCurrentError::ZeroDelay(passage.id));
        }
        if !self.sites.contains(passage.from.0) {
            return Err(ExactReceiverCurrentError::UnknownSite(passage.from));
        }
        if !self.sites.contains(passage.to.0) {
            return Err(ExactReceiverCurrentError::UnknownSite(passage.to));
        }
        if self.passages.contains(passage.id.0) {
            return Err(ExactReceiverCurrentError::DuplicatePassage(passage.id));
        }
        let passage_id = passage.id;
        let from = passage.from;
        let to = passage.to;
        self.passages
            .try_found(passage_id.0, passage)
            .map_err(|_| ExactReceiverCurrentError::CarrierExtent)?;
        self.sites
            .get_mut(from.0)
            .ok_or(ExactReceiverCurrentError::UnknownSite(from))?
            .outgoing
            .insert(passage_id);
        self.sites
            .get_mut(to.0)
            .ok_or(ExactReceiverCurrentError::UnknownSite(to))?
            .incoming
            .insert(passage_id);
        Ok(())
    }

    pub fn radiate(
        &self,
        sources: LocalSet<ReceiverCurrentSiteId>,
        targets: LocalSet<ReceiverCurrentSiteId>,
    ) -> Result<ExactReceiverCurrentRadiation, ExactReceiverCurrentError> {
        self.radiate_through(sources, targets, None)
    }

    /// Conduct one receiver-local forward survey through a declared chronology horizon.
    ///
    /// Unlike target radiation, this receiver does not first form the complete reverse-reachable
    /// population of a destination. It visits only sites reached from the supplied sources before
    /// `horizon`, retains equal-arrival predecessors in the same factorized body, and returns a
    /// later or cyclic arrival as deferred testimony. This is the lawful current for a navigable
    /// cover whose receiver does not yet know its terminal source occurrence.
    pub fn radiate_to_horizon(
        &self,
        sources: LocalSet<ReceiverCurrentSiteId>,
        horizon: u64,
    ) -> Result<ExactReceiverCurrentRadiation, ExactReceiverCurrentError> {
        self.radiate_to_horizon_through(sources, horizon, None)
    }

    /// Conduct one horizon-bounded survey through a receiver-declared site aperture.
    ///
    /// This is one owner-native restriction: sites outside `aperture` never enter the schedule,
    /// service dilation, predecessor incidence, or deferred-return body. Filtering a completed
    /// unrestricted radiation would not be equivalent because exterior branches would already
    /// have changed local capacity demand and chronology.
    pub fn radiate_to_horizon_in_aperture(
        &self,
        sources: LocalSet<ReceiverCurrentSiteId>,
        horizon: u64,
        aperture: &LocalSet<ReceiverCurrentSiteId>,
    ) -> Result<ExactReceiverCurrentRadiation, ExactReceiverCurrentError> {
        self.radiate_to_horizon_through(sources, horizon, Some(aperture))
    }

    fn radiate_to_horizon_through(
        &self,
        sources: LocalSet<ReceiverCurrentSiteId>,
        horizon: u64,
        aperture: Option<&LocalSet<ReceiverCurrentSiteId>>,
    ) -> Result<ExactReceiverCurrentRadiation, ExactReceiverCurrentError> {
        if sources.is_empty() {
            return Err(ExactReceiverCurrentError::EmptyRadiationBoundary);
        }
        for site in &sources {
            if !self.sites.contains(site.0)
                || aperture.is_some_and(|aperture| !aperture.contains(site))
            {
                return Err(ExactReceiverCurrentError::UnknownSite(*site));
            }
        }

        let mut arrivals = ExactReceiverCurrentArrivalAtlas::default();
        let mut schedule = LocalRelations::<u64, LocalSet<ReceiverCurrentSiteId>>::new();
        for source in &sources {
            arrivals.found(ExactReceiverCurrentArrival {
                site: *source,
                chronology: 0,
                population: BigUint::one(),
                predecessors: LocalSet::new(),
            })?;
            schedule_site(&mut schedule, 0, *source)?;
        }

        let mut passage_receipts = LocalSequence::new();
        let mut deferred_arrivals = LocalSet::new();
        let mut returned_targets = LocalSet::new();
        while let Some((&chronology, _)) = schedule.first() {
            if chronology > horizon {
                break;
            }
            let sites = schedule
                .remove(&chronology)
                .ok_or(ExactReceiverCurrentError::MalformedRadiation)?;
            for site in &sites {
                let site = *site;
                let Some(arrival) = arrivals.get(&site) else {
                    return Err(ExactReceiverCurrentError::MalformedRadiation);
                };
                let arrival_chronology = arrival.chronology;
                let branch_population = arrival.population.to_owned();
                if arrival_chronology != chronology {
                    continue;
                }
                returned_targets.insert(site);
                let standing = self
                    .sites
                    .get(site.0)
                    .ok_or(ExactReceiverCurrentError::UnknownSite(site))?;
                let mut active = LocalSequence::new();
                for passage in &standing.outgoing {
                    let passage = self
                        .passages
                        .get(passage.0)
                        .ok_or(ExactReceiverCurrentError::MalformedRadiation)?;
                    if aperture.is_none_or(|aperture| aperture.contains(&passage.to)) {
                        active.push(passage);
                    }
                }
                if active.is_empty() {
                    continue;
                }
                let site_capacity = standing.site.capacity.to_owned();
                let co_present_branch_population = &branch_population * BigUint::from(active.len());
                let service_rounds =
                    ceil_population_division(&co_present_branch_population, &site_capacity);
                let service_dilation = service_rounds
                    .to_u64()
                    .ok_or(ExactReceiverCurrentError::CarrierExtent)?
                    .checked_sub(1)
                    .ok_or(ExactReceiverCurrentError::MalformedRadiation)?;
                for passage in active {
                    let passage_delay = passage
                        .characteristic_delay
                        .checked_add(service_dilation)
                        .ok_or(ExactReceiverCurrentError::CarrierExtent)?;
                    let arrival_chronology = chronology
                        .checked_add(passage_delay)
                        .ok_or(ExactReceiverCurrentError::CarrierExtent)?;
                    let predecessor = ExactReceiverCurrentPredecessor {
                        from: site,
                        passage: passage.id,
                        departure_chronology: chronology,
                        passage_delay,
                    };
                    passage_receipts.push(ExactReceiverCurrentPassageReceipt {
                        passage: passage.id,
                        from: passage.from,
                        to: passage.to,
                        departure_chronology: chronology,
                        characteristic_delay: passage.characteristic_delay,
                        branch_population: branch_population.to_owned(),
                        co_present_branch_population: co_present_branch_population.to_owned(),
                        site_capacity: site_capacity.to_owned(),
                        service_rounds: service_rounds.to_owned(),
                        passage_delay,
                        arrival_chronology,
                    });
                    if arrival_chronology > horizon {
                        deferred_arrivals.insert(ExactReceiverCurrentDeferredArrival {
                            site: passage.to,
                            chronology: arrival_chronology,
                            population: branch_population.to_owned(),
                            predecessors: LocalSet::from([predecessor]),
                        });
                        continue;
                    }
                    match arrivals.get_mut(passage.to) {
                        None => {
                            arrivals.found(ExactReceiverCurrentArrival {
                                site: passage.to,
                                chronology: arrival_chronology,
                                population: branch_population.to_owned(),
                                predecessors: LocalSet::from([predecessor]),
                            })?;
                            schedule_site(&mut schedule, arrival_chronology, passage.to)?;
                        }
                        Some(prior) if arrival_chronology < prior.chronology => {
                            let prior_arrival = core::mem::replace(
                                prior,
                                ExactReceiverCurrentArrival {
                                    site: passage.to,
                                    chronology: arrival_chronology,
                                    population: branch_population.to_owned(),
                                    predecessors: LocalSet::from([predecessor]),
                                },
                            );
                            deferred_arrivals.insert(ExactReceiverCurrentDeferredArrival {
                                site: passage.to,
                                chronology: prior_arrival.chronology,
                                population: prior_arrival.population,
                                predecessors: prior_arrival.predecessors,
                            });
                            schedule_site(&mut schedule, arrival_chronology, passage.to)?;
                        }
                        Some(prior) if arrival_chronology == prior.chronology => {
                            prior.population += &branch_population;
                            prior.predecessors.insert(predecessor);
                        }
                        Some(_) => {
                            deferred_arrivals.insert(ExactReceiverCurrentDeferredArrival {
                                site: passage.to,
                                chronology: arrival_chronology,
                                population: branch_population.to_owned(),
                                predecessors: LocalSet::from([predecessor]),
                            });
                        }
                    }
                }
            }
        }
        passage_receipts.sort_by_key(|receipt| {
            (
                receipt.departure_chronology,
                receipt.arrival_chronology,
                receipt.passage,
            )
        });
        Ok(ExactReceiverCurrentRadiation {
            sources,
            requested_targets: LocalSet::new(),
            returned_targets,
            receiver_horizon: Some(horizon),
            arrivals,
            passage_receipts: passage_receipts.into_inner(),
            deferred_arrivals,
        })
    }

    /// Radiate through one receiver-declared local aperture of the standing ecology.
    ///
    /// The aperture does not copy or rebuild a subgraph. It restricts which already-founded
    /// sites and passages may conduct this occurrence while the complete current law remains
    /// mounted. Sources and targets must themselves belong to the aperture.
    pub fn radiate_in_aperture(
        &self,
        sources: LocalSet<ReceiverCurrentSiteId>,
        targets: LocalSet<ReceiverCurrentSiteId>,
        aperture: &LocalSet<ReceiverCurrentSiteId>,
    ) -> Result<ExactReceiverCurrentRadiation, ExactReceiverCurrentError> {
        self.radiate_through(sources, targets, Some(aperture))
    }

    fn radiate_through(
        &self,
        sources: LocalSet<ReceiverCurrentSiteId>,
        targets: LocalSet<ReceiverCurrentSiteId>,
        aperture: Option<&LocalSet<ReceiverCurrentSiteId>>,
    ) -> Result<ExactReceiverCurrentRadiation, ExactReceiverCurrentError> {
        if sources.is_empty() || targets.is_empty() {
            return Err(ExactReceiverCurrentError::EmptyRadiationBoundary);
        }
        for site in sources.iter().chain(&targets) {
            if !self.sites.contains(site.0) {
                return Err(ExactReceiverCurrentError::UnknownSite(*site));
            }
            if aperture.is_some_and(|aperture| !aperture.contains(site)) {
                return Err(ExactReceiverCurrentError::UnknownSite(*site));
            }
        }

        let target_reachable = self.target_reachable_sites(&targets, aperture);
        let mut arrivals = ExactReceiverCurrentArrivalAtlas::default();
        let mut schedule = LocalRelations::<u64, LocalSet<ReceiverCurrentSiteId>>::new();
        for source in &sources {
            arrivals.found(ExactReceiverCurrentArrival {
                site: *source,
                chronology: 0,
                population: BigUint::one(),
                predecessors: LocalSet::new(),
            })?;
            schedule_site(&mut schedule, 0, *source)?;
        }

        let mut passage_receipts = Vec::new();
        let mut deferred_arrivals = LocalSet::new();
        let mut returned_targets = LocalSet::new();
        let mut receiver_horizon = None::<u64>;

        while let Some((&chronology, _)) = schedule.first() {
            if receiver_horizon.is_some_and(|horizon| chronology > horizon) {
                break;
            }
            let sites = schedule
                .remove(&chronology)
                .ok_or(ExactReceiverCurrentError::MalformedRadiation)?;
            for site in &sites {
                let site = *site;
                let Some(arrival) = arrivals.get(&site) else {
                    return Err(ExactReceiverCurrentError::MalformedRadiation);
                };
                let arrival_chronology = arrival.chronology;
                let branch_population = arrival.population.clone();
                if arrival_chronology != chronology {
                    continue;
                }
                if targets.contains(&site) {
                    match receiver_horizon {
                        None => receiver_horizon = Some(chronology),
                        Some(horizon) if chronology < horizon => {
                            receiver_horizon = Some(chronology);
                            returned_targets.clear();
                        }
                        Some(_) => {}
                    }
                    if receiver_horizon == Some(chronology) {
                        returned_targets.insert(site);
                    }
                    continue;
                }
                if receiver_horizon.is_some_and(|horizon| chronology >= horizon) {
                    continue;
                }
                let standing = self
                    .sites
                    .get(site.0)
                    .ok_or(ExactReceiverCurrentError::UnknownSite(site))?;
                let mut active = Vec::new();
                for passage in &standing.outgoing {
                    let edge = self
                        .passages
                        .get(passage.0)
                        .ok_or(ExactReceiverCurrentError::MalformedRadiation)?;
                    if target_reachable.contains(&edge.to)
                        && aperture.is_none_or(|aperture| aperture.contains(&edge.to))
                    {
                        active.push(edge);
                    }
                }
                if active.is_empty() {
                    continue;
                }
                let site_capacity = standing.site.capacity.clone();
                let co_present_branch_population = &branch_population * BigUint::from(active.len());
                let service_rounds =
                    ceil_population_division(&co_present_branch_population, &site_capacity);
                let service_dilation = service_rounds
                    .to_u64()
                    .ok_or(ExactReceiverCurrentError::CarrierExtent)?
                    .checked_sub(1)
                    .ok_or(ExactReceiverCurrentError::MalformedRadiation)?;
                for passage in active {
                    let passage_delay = passage
                        .characteristic_delay
                        .checked_add(service_dilation)
                        .ok_or(ExactReceiverCurrentError::CarrierExtent)?;
                    let arrival_chronology = chronology
                        .checked_add(passage_delay)
                        .ok_or(ExactReceiverCurrentError::CarrierExtent)?;
                    let predecessor = ExactReceiverCurrentPredecessor {
                        from: site,
                        passage: passage.id,
                        departure_chronology: chronology,
                        passage_delay,
                    };
                    passage_receipts.push(ExactReceiverCurrentPassageReceipt {
                        passage: passage.id,
                        from: passage.from,
                        to: passage.to,
                        departure_chronology: chronology,
                        characteristic_delay: passage.characteristic_delay,
                        branch_population: branch_population.clone(),
                        co_present_branch_population: co_present_branch_population.clone(),
                        site_capacity: site_capacity.clone(),
                        service_rounds: service_rounds.clone(),
                        passage_delay,
                        arrival_chronology,
                    });
                    match arrivals.get_mut(passage.to) {
                        None => {
                            arrivals.found(ExactReceiverCurrentArrival {
                                site: passage.to,
                                chronology: arrival_chronology,
                                population: branch_population.clone(),
                                predecessors: LocalSet::from([predecessor]),
                            })?;
                            schedule_site(&mut schedule, arrival_chronology, passage.to)?;
                        }
                        Some(prior) if arrival_chronology < prior.chronology => {
                            let prior_arrival = core::mem::replace(
                                prior,
                                ExactReceiverCurrentArrival {
                                    site: passage.to,
                                    chronology: arrival_chronology,
                                    population: branch_population.clone(),
                                    predecessors: LocalSet::from([predecessor]),
                                },
                            );
                            deferred_arrivals.insert(ExactReceiverCurrentDeferredArrival {
                                site: passage.to,
                                chronology: prior_arrival.chronology,
                                population: prior_arrival.population,
                                predecessors: prior_arrival.predecessors,
                            });
                            schedule_site(&mut schedule, arrival_chronology, passage.to)?;
                        }
                        Some(prior) if arrival_chronology == prior.chronology => {
                            prior.population += &branch_population;
                            prior.predecessors.insert(predecessor);
                        }
                        Some(_) => {
                            deferred_arrivals.insert(ExactReceiverCurrentDeferredArrival {
                                site: passage.to,
                                chronology: arrival_chronology,
                                population: branch_population.clone(),
                                predecessors: LocalSet::from([predecessor]),
                            });
                        }
                    }
                }
            }
        }
        passage_receipts.sort_by_key(|receipt| {
            (
                receipt.departure_chronology,
                receipt.arrival_chronology,
                receipt.passage,
            )
        });
        Ok(ExactReceiverCurrentRadiation {
            sources,
            requested_targets: targets,
            returned_targets,
            receiver_horizon,
            arrivals,
            passage_receipts,
            deferred_arrivals,
        })
    }

    fn target_reachable_sites(
        &self,
        targets: &LocalSet<ReceiverCurrentSiteId>,
        aperture: Option<&LocalSet<ReceiverCurrentSiteId>>,
    ) -> LocalSet<ReceiverCurrentSiteId> {
        let mut reached = LocalSet::new();
        for target in targets {
            reached.insert(*target);
        }
        let mut frontier = LocalQueue::from_iter(targets.iter().copied());
        while let Some(site) = frontier.pop_front() {
            let Some(standing) = self.sites.get(site.0) else {
                continue;
            };
            for passage in &standing.incoming {
                let Some(edge) = self.passages.get(passage.0) else {
                    continue;
                };
                if aperture.is_some_and(|aperture| !aperture.contains(&edge.from)) {
                    continue;
                }
                if reached.insert(edge.from) {
                    frontier.push_back(edge.from);
                }
            }
        }
        reached
    }
}

fn schedule_site(
    schedule: &mut LocalRelations<u64, LocalSet<ReceiverCurrentSiteId>>,
    chronology: u64,
    site: ReceiverCurrentSiteId,
) -> Result<(), ExactReceiverCurrentError> {
    if let Some(sites) = schedule.get_mut(&chronology) {
        sites.insert(site);
        return Ok(());
    }
    let mut sites = LocalSet::new();
    sites.insert(site);
    schedule
        .try_insert(chronology, sites)
        .map_err(|_| ExactReceiverCurrentError::CarrierExtent)?;
    Ok(())
}

fn ceil_population_division(population: &BigUint, capacity: &BigUint) -> BigUint {
    debug_assert!(!population.is_zero());
    debug_assert!(!capacity.is_zero());
    (population + capacity - BigUint::one()) / capacity
}

#[cfg(test)]
mod tests {
    use super::*;

    fn site(at: u64) -> ReceiverCurrentSiteId {
        ReceiverCurrentSiteId(at)
    }

    fn passage(at: u64, from: u64, to: u64) -> ExactReceiverCurrentPassage {
        ExactReceiverCurrentPassage {
            id: ReceiverCurrentPassageId(at),
            from: site(from),
            to: site(to),
            characteristic_delay: 1,
        }
    }

    #[test]
    fn recurrent_capacity_dilates_a_congested_hub_without_ranking_its_branches() {
        let mut law = ExactReceiverCurrentLaw::new();
        for at in 0..5 {
            law.found_site(site(at), BigUint::one()).unwrap();
        }
        for edge in [
            passage(0, 0, 1),
            passage(1, 1, 4),
            passage(2, 1, 2),
            passage(3, 1, 3),
            passage(4, 2, 4),
            passage(5, 3, 4),
        ] {
            law.found_passage(edge).unwrap();
        }
        let sources = LocalSet::from([site(0)]);
        let targets = LocalSet::from([site(4)]);
        let congested = law.radiate(sources.clone(), targets.clone()).unwrap();
        assert_eq!(congested.receiver_horizon, Some(4));
        let hub_departures = congested
            .passage_receipts
            .iter()
            .filter(|receipt| receipt.from == site(1))
            .collect::<Vec<_>>();
        assert_eq!(hub_departures.len(), 3);
        assert!(
            hub_departures
                .iter()
                .all(|receipt| receipt.service_rounds == BigUint::from(3_u8))
        );

        law.set_site_capacity(site(1), BigUint::from(3_u8)).unwrap();
        let conditioned = law.radiate(sources, targets).unwrap();
        assert_eq!(conditioned.receiver_horizon, Some(2));
        assert!(
            conditioned
                .passage_receipts
                .iter()
                .filter(|receipt| receipt.from == site(1))
                .all(|receipt| receipt.service_rounds == BigUint::one())
        );
    }

    #[test]
    fn equal_arrivals_retain_two_witness_paths_instead_of_enacting_their_union() {
        let mut law = ExactReceiverCurrentLaw::new();
        law.found_site(site(0), BigUint::from(2_u8)).unwrap();
        for at in 1..4 {
            law.found_site(site(at), BigUint::one()).unwrap();
        }
        for edge in [
            passage(0, 0, 1),
            passage(1, 0, 2),
            passage(2, 1, 3),
            passage(3, 2, 3),
        ] {
            law.found_passage(edge).unwrap();
        }
        let radiation = law
            .radiate(LocalSet::from([site(0)]), LocalSet::from([site(3)]))
            .unwrap();
        assert_eq!(radiation.receiver_horizon, Some(2));
        assert_eq!(
            radiation.exact_path_population(site(3)),
            BigUint::from(2_u8)
        );
        let witnesses = radiation.witness_paths_to(site(3)).unwrap();
        assert_eq!(witnesses.len(), 2);
        assert_eq!(witnesses[0].sites, vec![site(0), site(1), site(3)]);
        assert_eq!(witnesses[1].sites, vec![site(0), site(2), site(3)]);
    }

    #[test]
    fn a_receiver_section_crosses_an_exponential_path_body_without_enumerating_it() {
        const DIAMONDS: u64 = 64;
        let mut law = ExactReceiverCurrentLaw::new();
        law.found_site(site(0), BigUint::one() << (DIAMONDS + 2))
            .unwrap();
        let mut passage_at = 0_u64;
        let mut join = 0_u64;
        for diamond in 0..DIAMONDS {
            let left = 1 + diamond * 3;
            let right = left + 1;
            let next_join = left + 2;
            for at in [left, right, next_join] {
                law.found_site(site(at), BigUint::one() << (DIAMONDS + 2))
                    .unwrap();
            }
            for (from, to) in [
                (join, left),
                (join, right),
                (left, next_join),
                (right, next_join),
            ] {
                law.found_passage(passage(passage_at, from, to)).unwrap();
                passage_at += 1;
            }
            join = next_join;
        }

        let radiation = law
            .radiate(LocalSet::from([site(0)]), LocalSet::from([site(join)]))
            .unwrap();
        let population = BigUint::one() << DIAMONDS;
        assert_eq!(radiation.exact_path_population(site(join)), population);
        let last = radiation
            .witness_section_to(site(join), &(population - BigUint::one()))
            .unwrap();
        assert_eq!(last.sites.len(), usize::try_from(DIAMONDS * 2 + 1).unwrap());
        assert_eq!(last.passages.len(), usize::try_from(DIAMONDS * 2).unwrap());
    }

    #[test]
    fn a_receiver_aperture_restricts_the_mounted_current_without_rebuilding_it() {
        let mut law = ExactReceiverCurrentLaw::new();
        law.found_site(site(0), BigUint::from(2_u8)).unwrap();
        for at in 1..4 {
            law.found_site(site(at), BigUint::one()).unwrap();
        }
        for edge in [
            passage(0, 0, 1),
            passage(1, 1, 3),
            passage(2, 0, 2),
            passage(3, 2, 3),
        ] {
            law.found_passage(edge).unwrap();
        }

        let complete = law
            .radiate(LocalSet::from([site(0)]), LocalSet::from([site(3)]))
            .unwrap();
        assert_eq!(complete.exact_path_population(site(3)), BigUint::from(2_u8));

        let aperture = LocalSet::from([site(0), site(2), site(3)]);
        let restricted = law
            .radiate_in_aperture(
                LocalSet::from([site(0)]),
                LocalSet::from([site(3)]),
                &aperture,
            )
            .unwrap();
        let witnesses = restricted.witness_paths_to(site(3)).unwrap();
        assert_eq!(witnesses.len(), 1);
        assert_eq!(witnesses[0].sites, vec![site(0), site(2), site(3)]);
        assert_eq!(law.passages().count(), 4);
    }

    #[test]
    fn a_cycle_returns_as_a_deferred_arrival_not_an_infinite_schedule() {
        let mut law = ExactReceiverCurrentLaw::new();
        for at in 0..3 {
            law.found_site(site(at), BigUint::from(2_u8)).unwrap();
        }
        for edge in [passage(0, 0, 1), passage(1, 1, 0), passage(2, 1, 2)] {
            law.found_passage(edge).unwrap();
        }
        let radiation = law
            .radiate(LocalSet::from([site(0)]), LocalSet::from([site(2)]))
            .unwrap();
        assert_eq!(radiation.receiver_horizon, Some(2));
        assert!(
            radiation
                .deferred_arrivals
                .iter()
                .any(|arrival| arrival.site == site(0) && arrival.chronology == 2)
        );
    }

    #[test]
    fn a_forward_horizon_touches_only_the_source_local_star_and_retains_its_boundary() {
        let mut law = ExactReceiverCurrentLaw::new();
        for at in 0..7 {
            law.found_site(site(at), BigUint::from(4_u8)).unwrap();
        }
        for edge in [
            passage(0, 0, 1),
            passage(1, 0, 2),
            passage(2, 1, 3),
            passage(3, 2, 3),
            passage(4, 3, 4),
            passage(5, 5, 6),
        ] {
            law.found_passage(edge).unwrap();
        }

        let survey = law
            .radiate_to_horizon(LocalSet::from([site(0)]), 2)
            .unwrap();
        assert_eq!(survey.receiver_horizon, Some(2));
        assert_eq!(survey.exact_path_population(site(3)), BigUint::from(2_u8));
        assert!(survey.returned_targets.contains(&site(3)));
        assert!(!survey.returned_targets.contains(&site(4)));
        assert!(!survey.returned_targets.contains(&site(5)));
        assert!(
            survey
                .deferred_arrivals
                .iter()
                .any(|arrival| arrival.site == site(4) && arrival.chronology == 3)
        );
        assert!(survey.arrivals.get(&site(5)).is_none());
        assert_eq!(survey.witness_paths_to(site(3)).unwrap().len(), 2);
    }
}
