//! Historical Holon/contact-cycle compatibility over an immutable receiver-before surface.
//!
//! Every admitted current receives its own body, carrier, OWN topology, consequence aperture, and
//! emission partition while reading the same standing field.  Only after every current closes are
//! the parts joined, recurrent spans materialized once, and every supplied cut prepared.  Commit is
//! an owner transition: a world-supplied cut ordinal installs its already-formed successor and the
//! complete enacted population together, or changes nothing.
//!
//! This module retains complete observer testimony and recovery for historical world clients.  It
//! is not the production execution boundary. [`crate::LiveCurrentMachine`] owns the direct live
//! transition; no physical executor is injected through this compatibility lifecycle.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use body::channel::LineageChannel;
use body::manifold::{compose_place, ErosBody, LiveBodyHeader, Node, TermCounts};
use soma_abi::active::DirectedIncidence;
use soma_abi::emission::DeedEmission;
use soma_abi::holon::{
    LineageIncidenceRow, ReturnOriginRow, SilentReceipt, SourceDispositionRow, TransitionReceipt,
};

use crate::active_topology::{prepare_sparse_fold_from_owned, ActiveTopology, ActiveTopologyError};
use crate::event_mouth::{
    conduct_current_partition_with_event_receiver, preflight_current_partition_validated,
};
use crate::recovery::{
    CurrentMountImage, CurrentOutcomeImage, EcologyCheckpoint, EnactedPopulationImage,
    LineageStateImage, PreparedCutImage, ECOLOGY_CHECKPOINT_VERSION,
};
use crate::{
    ActiveCut, ActiveCutError, CarriedSpanSurface, ConductError, CurrentConduct,
    DirectedCutContact, EmissionJournal, EmissionJournalError, EventContact, EventSurface,
    EventSurfaceError, EventTopology, FoldedCut, GrowingCarrier, GrowingRankedOwn, HolonError,
    LiveCarrierSnapshot, LiveHolon, RankedOwnCell, SparseStandingError, SparseStandingSurface,
    TransitionId,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ContactCycleError {
    Active(ActiveCutError),
    Conduct(ConductError),
    Emission(EmissionJournalError),
    Topology(ActiveTopologyError),
    EventSurface(EventSurfaceError),
    Standing(SparseStandingError),
    ResourceExtent,
    ResourceReservation,
    CurrentBirth(u64),
    CurrentSchedule(u64),
    DirectedUnresolved(u64),
    CurrentMountExtent,
    LineageAbsent(u64),
    ForeignLineage(u64),
    DuplicateLineage(u64),
    LineageClaimed(u64),
    CutAbsent(u64),
    ReceiverChanged,
    LiveInterval,
    RecoveryIdentity,
    RecoveryDuplicate,
    RecoveryCarrier,
    RecoveryVersion,
    RecoveryTopology,
    SettlementSourceExtent {
        expected: u64,
        actual: u64,
    },
    SettlementReturnExtent {
        expected: u64,
        actual: u64,
    },
    SettlementUnresolved(u64),
    SettlementContact(u64),
    SettlementLineageOutOfRange {
        source_incidence: u64,
        source_event_offset: u64,
        returned_incidence: u64,
        returned_event_offset: u64,
    },
    SettlementLineageNotContacted {
        source_incidence: u64,
        source_event_offset: u64,
    },
    SettlementLineageAbsent {
        source_current: u64,
        returned_current: u64,
    },
    SettlementReturnTarget(u64),
    SettlementReturnOrigin(u64),
    SettlementReturnMount(u64),
    Holon(HolonError),
}

/// Caller-supplied durable identity of one live ecology.  It is provenance for exact capability
/// recovery, never an input to Soma conduct and never generated from material content.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EcologyId {
    high: u64,
    low: u64,
}

impl EcologyId {
    pub const fn new(high: u64, low: u64) -> Self {
        Self { high, low }
    }

    pub const fn words(self) -> [u64; 2] {
        [self.high, self.low]
    }
}

/// Stable address of one current-local lineage.  Reopen resolves this row through the ecology's
/// one instantiated enacted-population table; raw pointers and storage order never cross SLEEP.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LineageHandle {
    ecology: EcologyId,
    enactment: u64,
    current: u64,
}

/// Typed rest testimony for one exact current-local continuation. The native carrier words are a
/// persistence face only; recovery remounts their validated construction and never feeds these
/// words back as relation atoms.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LineageImage {
    handle: LineageHandle,
    native_carrier: Vec<u32>,
    parents: Vec<LineageHandle>,
}

impl LineageImage {
    pub fn handle(&self) -> LineageHandle {
        self.handle
    }

    pub fn native_carrier_words(&self) -> &[u32] {
        &self.native_carrier
    }

    /// Exact causal ancestry carried by this active lineage. Parent handles remain testimony even
    /// where the parent carrier has lawfully continued or ended and is no longer live.
    pub fn parents(&self) -> &[LineageHandle] {
        &self.parents
    }
}

/// Complete active ecology face at an exact quiescent boundary. World-organ material remains in
/// its own checkpoint; this image carries only Soma standing construction and unclaimed live
/// continuation capabilities.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EcologyRestImage {
    id: EcologyId,
    generation: u64,
    next_enactment: u64,
    standing: SparseStandingSurface,
    lineages: Vec<LineageImage>,
}

impl EcologyRestImage {
    pub fn id(&self) -> EcologyId {
        self.id
    }

    pub fn generation(&self) -> u64 {
        self.generation
    }

    pub fn standing(&self) -> &SparseStandingSurface {
        &self.standing
    }

    pub fn lineages(&self) -> &[LineageImage] {
        &self.lineages
    }
}

impl LineageHandle {
    pub const fn ecology(self) -> EcologyId {
        self.ecology
    }

    pub const fn enactment(self) -> u64 {
        self.enactment
    }

    pub const fn current(self) -> u64 {
        self.current
    }
}

impl From<ActiveCutError> for ContactCycleError {
    fn from(error: ActiveCutError) -> Self {
        Self::Active(error)
    }
}

impl From<ConductError> for ContactCycleError {
    fn from(error: ConductError) -> Self {
        Self::Conduct(error)
    }
}

impl From<EmissionJournalError> for ContactCycleError {
    fn from(error: EmissionJournalError) -> Self {
        Self::Emission(error)
    }
}

impl From<ActiveTopologyError> for ContactCycleError {
    fn from(error: ActiveTopologyError) -> Self {
        Self::Topology(error)
    }
}

impl From<EventSurfaceError> for ContactCycleError {
    fn from(error: EventSurfaceError) -> Self {
        Self::EventSurface(error)
    }
}

impl From<SparseStandingError> for ContactCycleError {
    fn from(error: SparseStandingError) -> Self {
        Self::Standing(error)
    }
}

impl From<HolonError> for ContactCycleError {
    fn from(error: HolonError) -> Self {
        Self::Holon(error)
    }
}

/// Whole consequence of one independently enacted current.  Scalar counts remain beside the
/// exact contacts, OWN cells, channel, and carrier; none substitutes for another.
pub struct CurrentOutcome {
    conduct: CurrentConduct,
    contacts: Vec<EventContact>,
    own_rank: u64,
    own_occupancy: Vec<u64>,
    breath: (u64, u64),
    own_cells: Vec<RankedOwnCell>,
    terms: TermCounts,
    /// Exact live carrier, including co-presence beyond the historical flat/card row. The carried
    /// frame remains the canonical header and compatibility prefix; neither is complete alone.
    carrier: Arc<LiveCarrierSnapshot>,
    thoughts: u32,
}

impl CurrentOutcome {
    pub fn conduct(&self) -> CurrentConduct {
        self.conduct
    }

    pub fn contacts(&self) -> &[EventContact] {
        &self.contacts
    }

    pub fn own_rank(&self) -> u64 {
        self.own_rank
    }

    /// Historical flat projection only. A deep ranked chart returns no fabricated axis.
    pub fn flat_own_axis(&self) -> Option<u32> {
        (self.own_rank <= 16).then(|| 1u32 << self.own_rank)
    }

    pub fn own_occupancy_words(&self) -> &[u64] {
        &self.own_occupancy
    }

    pub fn own_occupancy_u64(&self) -> Option<u64> {
        match self.own_occupancy.as_slice() {
            [] => Some(0),
            [word] => Some(*word),
            _ => None,
        }
    }

    pub fn breath(&self) -> (u64, u64) {
        self.breath
    }

    pub fn own_cells(&self) -> &[RankedOwnCell] {
        &self.own_cells
    }

    pub fn channel(&self) -> LineageChannel {
        self.carrier.header().channel()
    }

    pub fn terms(&self) -> TermCounts {
        self.terms
    }

    pub fn carrier_depth(&self) -> usize {
        self.carrier.carrier().depth()
    }

    pub fn carrier(&self) -> &[u32] {
        self.carrier.carrier().words()
    }

    pub fn carrier_state(&self) -> &GrowingCarrier {
        self.carrier.carrier()
    }

    pub fn live_header(&self) -> LiveBodyHeader {
        self.carrier.header()
    }

    pub fn thoughts(&self) -> u32 {
        self.thoughts
    }

    fn checkpoint_image(&self) -> Result<CurrentOutcomeImage, ContactCycleError> {
        Ok(CurrentOutcomeImage {
            conduct: self.conduct,
            contacts: self.contacts.clone(),
            own_rank: self.own_rank,
            own_occupancy: self.own_occupancy.clone(),
            breath: self.breath,
            own_cells: self.own_cells.clone(),
            terms: self.terms,
            native_carrier: self
                .carrier
                .encode_native_words()
                .map_err(|_| ContactCycleError::RecoveryCarrier)?,
            thoughts: self.thoughts,
        })
    }

    fn from_checkpoint_image(image: CurrentOutcomeImage) -> Result<Self, ContactCycleError> {
        let carrier = Arc::new(
            LiveCarrierSnapshot::from_native_words(&image.native_carrier)
                .map_err(|_| ContactCycleError::RecoveryCarrier)?,
        );
        if image
            .own_cells
            .iter()
            .any(|cell| cell.address().rank() != image.own_rank)
        {
            return Err(ContactCycleError::RecoveryTopology);
        }
        Ok(Self {
            conduct: image.conduct,
            contacts: image.contacts,
            own_rank: image.own_rank,
            own_occupancy: image.own_occupancy,
            breath: image.breath,
            own_cells: image.own_cells,
            terms: image.terms,
            carrier,
            thoughts: image.thoughts,
        })
    }
}

pub struct PreparedCut {
    cut: u64,
    fold: FoldedCut,
    successor: Arc<SparseStandingSurface>,
}

impl PreparedCut {
    pub fn cut(&self) -> u64 {
        self.cut
    }

    pub fn fold(&self) -> &FoldedCut {
        &self.fold
    }

    pub fn successor(&self) -> Option<&SparseStandingSurface> {
        Some(&self.successor)
    }
}

/// The complete once-enacted active population.  The source cut and its opaque origins remain
/// mounted beside current interiors, exact deeds, shared carried spans, plural incidence, directed
/// hand, and every prepared receiver cut.
pub struct EnactedPopulation {
    active: Arc<ActiveCut>,
    event_surfaces: Vec<EventSurface>,
    emissions: EmissionJournal,
    currents: Vec<CurrentOutcome>,
    carried: Vec<CarriedSpanSurface>,
    incidence_surface: Vec<usize>,
    directed_contacts: Vec<DirectedCutContact>,
    prepared_cut: Option<PreparedCut>,
    mounts: Vec<CurrentMount>,
    lineages: Vec<Arc<LineageState>>,
}

struct EnactedRecoverySeed {
    enactment: u64,
    active: Arc<ActiveCut>,
    event_surfaces: Vec<EventSurface>,
    emissions: EmissionJournal,
    currents: Vec<CurrentOutcome>,
    carried: Vec<CarriedSpanSurface>,
    incidence_surface: Vec<usize>,
    directed_contacts: Vec<DirectedCutContact>,
    prepared_cut: Option<PreparedCut>,
    mounts: Vec<CurrentMountImage>,
    lineages: Vec<LineageStateImage>,
}

struct EcologyOwner {
    id: EcologyId,
}

struct LineageState {
    handle: LineageHandle,
    carrier: Arc<LiveCarrierSnapshot>,
    parents: Vec<LineageHandle>,
    claimed: AtomicBool,
}

impl LineageState {
    fn image(&self) -> Result<LineageImage, ContactCycleError> {
        Ok(LineageImage {
            handle: self.handle,
            native_carrier: self
                .carrier
                .encode_native_words()
                .map_err(|_| ContactCycleError::RecoveryCarrier)?,
            parents: self.parents.clone(),
        })
    }
}

/// One exact current-local construction carried by actual world incidence into a later cut.  This
/// is a live owner reference, not a source label, similarity lookup, cache key, or scheduler hand.
/// Only an enacted population can issue it, and the selected current remains mounted whole.
#[derive(Clone)]
pub struct LineageRef {
    owner: Arc<EcologyOwner>,
    state: Arc<LineageState>,
}

impl LineageRef {
    fn carrier(&self) -> &LiveCarrierSnapshot {
        &self.state.carrier
    }

    pub fn durable_handle(&self) -> LineageHandle {
        self.state.handle
    }

    pub fn checkpoint(&self) -> Result<LineageImage, ContactCycleError> {
        self.state.image()
    }

    pub fn parents(&self) -> &[LineageHandle] {
        &self.state.parents
    }
}

/// Exact contact state of one current at the enacted source boundary. It is derived solely from
/// ordinary emitted incidence and supplied causal hand; no modality, score, or world label enters.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CurrentContactState {
    contacted: bool,
    unresolved: bool,
}

impl CurrentContactState {
    pub const fn contacted(self) -> bool {
        self.contacted
    }

    pub const fn unresolved(self) -> bool {
        self.unresolved
    }

    pub const fn settled_silent(self) -> bool {
        !self.contacted && !self.unresolved
    }
}

/// Exact fate of one source carrier. This describes continuity, never truth, reward, or whether
/// the source's material law accepted its consequence.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SourceDisposition {
    Standing,
    Continued(u64),
    Ended,
}

impl SourceDisposition {
    pub const fn abi(self) -> SourceDispositionRow {
        match self {
            Self::Standing => SourceDispositionRow::standing(),
            Self::Continued(current) => SourceDispositionRow::continued(current),
            Self::Ended => SourceDispositionRow::ended(),
        }
    }
}

/// Exact physical carrier origin of one returned current. Plural causal ancestry remains separate
/// so split and merge do not choose a parent or concatenate bodies.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReturnOrigin {
    Continued(u64),
    Birth,
}

impl ReturnOrigin {
    pub const fn abi(self) -> ReturnOriginRow {
        match self {
            Self::Continued(current) => ReturnOriginRow::continued(current),
            Self::Birth => ReturnOriginRow::birth(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct LineageIncidence {
    source_incidence: u64,
    source_event_offset: u64,
    returned_incidence: u64,
    returned_event_offset: u64,
}

impl LineageIncidence {
    pub const fn new(
        source_incidence: u64,
        source_event_offset: u64,
        returned_incidence: u64,
        returned_event_offset: u64,
    ) -> Self {
        Self {
            source_incidence,
            source_event_offset,
            returned_incidence,
            returned_event_offset,
        }
    }

    pub const fn source_incidence(self) -> u64 {
        self.source_incidence
    }

    pub const fn source_event_offset(self) -> u64 {
        self.source_event_offset
    }

    pub const fn returned_incidence(self) -> u64 {
        self.returned_incidence
    }

    pub const fn returned_event_offset(self) -> u64 {
        self.returned_event_offset
    }

    pub const fn abi(self) -> LineageIncidenceRow {
        LineageIncidenceRow::new(
            self.source_incidence,
            self.source_event_offset,
            self.returned_incidence,
            self.returned_event_offset,
        )
    }
}

/// Complete sparse lineage boundary supplied by the world for one returned settlement. Validation
/// against actual contact, mounts, and live source capabilities occurs atomically at closure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SettlementPlan {
    source: Vec<SourceDisposition>,
    origins: Vec<ReturnOrigin>,
    lineages: Vec<LineageIncidence>,
}

#[derive(Clone, Copy)]
struct ResolvedLineageIncidence {
    source_current: u64,
    returned_current: u64,
}

fn cut_incidence_event(
    active: &ActiveCut,
    cut: u64,
    local_incidence: u64,
    event_offset: u64,
) -> Option<(u64, u64)> {
    let cut = *active.cuts.get(usize::try_from(cut).ok()?)?;
    if local_incidence >= cut.incidences() {
        return None;
    }
    let incidence = *active
        .incidences
        .get(usize::try_from(cut.incidence_offset().checked_add(local_incidence)?).ok()?)?;
    if event_offset >= incidence.current_events() {
        return None;
    }
    let current = *active
        .currents
        .get(usize::try_from(incidence.current()).ok()?)?;
    let event = current
        .event_offset()
        .checked_add(incidence.current_event_offset())?
        .checked_add(event_offset)?;
    Some((incidence.current(), event))
}

impl SettlementPlan {
    pub fn new(
        source: Vec<SourceDisposition>,
        origins: Vec<ReturnOrigin>,
        lineages: Vec<LineageIncidence>,
    ) -> Self {
        Self {
            source,
            origins,
            lineages,
        }
    }

    pub fn source_dispositions(&self) -> &[SourceDisposition] {
        &self.source
    }

    pub fn return_origins(&self) -> &[ReturnOrigin] {
        &self.origins
    }

    pub fn lineage_incidences(&self) -> &[LineageIncidence] {
        &self.lineages
    }

    fn abi_populations(
        &self,
    ) -> Result<
        (
            Vec<SourceDispositionRow>,
            Vec<ReturnOriginRow>,
            Vec<LineageIncidenceRow>,
        ),
        ContactCycleError,
    > {
        let mut sources = Vec::new();
        sources
            .try_reserve_exact(self.source.len())
            .map_err(|_| ContactCycleError::ResourceReservation)?;
        sources.extend(self.source.iter().copied().map(SourceDisposition::abi));
        let mut origins = Vec::new();
        origins
            .try_reserve_exact(self.origins.len())
            .map_err(|_| ContactCycleError::ResourceReservation)?;
        origins.extend(self.origins.iter().copied().map(ReturnOrigin::abi));
        let mut lineages = Vec::new();
        lineages
            .try_reserve_exact(self.lineages.len())
            .map_err(|_| ContactCycleError::ResourceReservation)?;
        lineages.extend(self.lineages.iter().copied().map(LineageIncidence::abi));
        Ok((sources, origins, lineages))
    }
}

/// One exact plural sheet which actually occupied a receiving edge.  This is deliberately
/// separate from [`LineageRef`]: a lineage carries one ordered `K`, while a cut carries the
/// partial-order relation among every incidence which met there.  The capability owns neither a
/// copied body nor an interpreted graph; it only keeps the enacted population and the selected
/// cut alive together.
#[derive(Clone)]
pub struct CarriedCutRef {
    owner: Arc<EcologyOwner>,
    enacted: Arc<EnactedPopulation>,
    cut: u64,
}

impl CarriedCutRef {
    pub fn cut(&self) -> u64 {
        self.cut
    }

    pub fn active(&self) -> &Arc<ActiveCut> {
        self.enacted.active()
    }

    /// Live-owner equality only.  This is an attachment check, not content identity or a durable
    /// lineage identifier.
    pub fn shares_live_ecology(&self, other: &CarriedCutRef) -> bool {
        Arc::ptr_eq(&self.owner, &other.owner)
    }

    pub fn emissions(&self) -> &EmissionJournal {
        self.enacted.emissions()
    }

    /// Exact enacted outcome of one current. This is a world-facing causal surface, not a score:
    /// an organ may use its actual event contacts and deeds under its own material law.
    pub fn current_outcome(&self, current: u64) -> Option<&CurrentOutcome> {
        self.enacted.currents().get(usize::try_from(current).ok()?)
    }

    pub fn event_surface(&self, event: u64) -> Option<EventSurface> {
        self.enacted.event_surface(event)
    }

    /// Return the resolving event contact which actually crossed, if this event was bright. A
    /// wholly static event lawfully has no `EventContact`; its action remains in the journaled
    /// interval and current accounting.
    pub fn event_contact(&self, event: u64) -> Option<EventContact> {
        self.enacted
            .currents()
            .iter()
            .flat_map(|current| current.contacts())
            .find(|contact| contact.event == event)
            .copied()
    }

    /// Every accepted deed causally emitted by one source event. An exact empty slice means this
    /// event emitted no deed; absence means the event ordinal is outside the enacted population.
    pub fn event_deeds(&self, event: u64) -> Option<&[DeedEmission]> {
        let span = *self
            .enacted
            .emissions()
            .events
            .get(usize::try_from(event).ok()?)?;
        let first = usize::try_from(span.deed_offset()).ok()?;
        let after = usize::try_from(span.deed_offset().checked_add(span.deeds())?).ok()?;
        self.enacted.emissions().deeds.get(first..after)
    }

    pub fn incidence_count(&self) -> u64 {
        self.enacted.active().cuts[self.cut as usize].incidences()
    }

    /// Resolve one cut-local incidence to the already-carried source surface.  Repetition remains
    /// plural because `local` is not replaced by the shared surface ordinal.
    pub fn incidence_surface(&self, local: u64) -> Option<&CarriedSpanSurface> {
        let cut = self
            .enacted
            .active()
            .cuts
            .get(usize::try_from(self.cut).ok()?)?;
        if local >= cut.incidences() {
            return None;
        }
        let global = cut.incidence_offset().checked_add(local)?;
        self.enacted.surface_for_incidence(global)
    }

    /// Resolve one cut-local physical incidence/event occurrence. The returned event ordinal is
    /// global only within this mounted ActiveCut; it is never a semantic or storage identity.
    pub fn incidence_event(&self, local: u64, event_offset: u64) -> Option<(u64, u64)> {
        cut_incidence_event(self.enacted.active(), self.cut, local, event_offset)
    }

    /// Whether this exact physical event occurrence participated in actual emitted or crossed
    /// contact. Repeated incidences borrowing one event remain distinguishable through `local`.
    pub fn incidence_event_contacted(&self, local: u64, event_offset: u64) -> Option<bool> {
        let (_, event) = self.incidence_event(local, event_offset)?;
        if self
            .event_deeds(event)
            .is_some_and(|deeds| !deeds.is_empty())
        {
            return Some(true);
        }
        let cut = *self
            .enacted
            .active()
            .cuts
            .get(usize::try_from(self.cut).ok()?)?;
        let incidence_global = cut.incidence_offset().checked_add(local)?;
        for directed_local in 0..cut.directed() {
            let edge =
                *self.enacted.active().directed.get(
                    usize::try_from(cut.directed_offset().checked_add(directed_local)?).ok()?,
                )?;
            if edge.from_incidence() != incidence_global && edge.to_incidence() != incidence_global
            {
                continue;
            }
            if matches!(
                self.directed_contact(directed_local)?.resolution(),
                crate::DirectedResolution::Crossed(_)
            ) {
                return Some(true);
            }
        }
        Some(false)
    }

    /// The source-supplied causal hand, in its lived edge order.  Consumers may form oriented A2
    /// relations from these endpoint references; iteration order itself is never a cause.
    pub fn directed(&self) -> &[DirectedIncidence] {
        let cut = &self.enacted.active().cuts[self.cut as usize];
        if cut.directed() == 0 {
            return &[];
        }
        let first = cut.directed_offset() as usize;
        let after = first + cut.directed() as usize;
        &self.enacted.active().directed[first..after]
    }

    /// Resolve one cut-local supplied hand to its enacted oriented contact. `None` means the local
    /// ordinal is outside this cut; open fourth contacts and plural endpoint residuals remain
    /// explicit [`DirectedResolution`] values inside the returned row.
    pub fn directed_contact(&self, local: u64) -> Option<DirectedCutContact> {
        let cut = self
            .enacted
            .active()
            .cuts
            .get(usize::try_from(self.cut).ok()?)?;
        if local >= cut.directed() {
            return None;
        }
        let global = cut.directed_offset().checked_add(local)?;
        self.enacted
            .directed_contacts()
            .get(usize::try_from(global).ok()?)
            .copied()
    }

    /// Derive whether one current actually contacted this cut, remained open, or lawfully stood
    /// silent. Deed extent and crossed supplied hand are the physical evidence; mere transaction
    /// membership is not world actuation.
    pub fn current_contact_state(&self, current: u64) -> Option<CurrentContactState> {
        if current >= self.enacted.active().header.currents() {
            return None;
        }
        let active = self.enacted.active();
        let cut = *active.cuts.get(usize::try_from(self.cut).ok()?)?;
        let mut contacted = false;
        let mut unresolved = false;

        for local in 0..cut.incidences() {
            let incidence = *active
                .incidences
                .get(usize::try_from(cut.incidence_offset().checked_add(local)?).ok()?)?;
            if incidence.current() == current
                && self
                    .incidence_surface(local)
                    .is_some_and(|surface| surface.deeds() != 0)
            {
                contacted = true;
            }
        }

        for local in 0..cut.directed() {
            let edge = *active
                .directed
                .get(usize::try_from(cut.directed_offset().checked_add(local)?).ok()?)?;
            let from = *active
                .incidences
                .get(usize::try_from(edge.from_incidence()).ok()?)?;
            let to = *active
                .incidences
                .get(usize::try_from(edge.to_incidence()).ok()?)?;
            if from.current() != current && to.current() != current {
                continue;
            }
            match self.directed_contact(local)?.resolution() {
                crate::DirectedResolution::Crossed(_) => contacted = true,
                crate::DirectedResolution::SpanEndpointOpen => unresolved = true,
                crate::DirectedResolution::FourthContactOpen(_) => {}
            }
        }
        Some(CurrentContactState {
            contacted,
            unresolved,
        })
    }
}

/// Exact current birth/continuation relation supplied by the active world. Every current declares
/// one of these; absence is not silently interpreted as either case.
#[derive(Clone)]
pub enum CurrentMount {
    Birth,
    Continue(LineageRef),
}

impl EnactedPopulation {
    fn checkpoint_image(&self) -> Result<EnactedPopulationImage, ContactCycleError> {
        let enactment = self
            .lineages
            .first()
            .map(|lineage| lineage.handle.enactment)
            .ok_or(ContactCycleError::RecoveryTopology)?;
        if self
            .lineages
            .iter()
            .any(|lineage| lineage.handle.enactment != enactment)
        {
            return Err(ContactCycleError::RecoveryTopology);
        }
        let currents = self
            .currents
            .iter()
            .map(CurrentOutcome::checkpoint_image)
            .collect::<Result<Vec<_>, _>>()?;
        let incidence_surface = self
            .incidence_surface
            .iter()
            .map(|surface| u64::try_from(*surface).map_err(|_| ContactCycleError::ResourceExtent))
            .collect::<Result<Vec<_>, _>>()?;
        let mounts = self
            .mounts
            .iter()
            .map(|mount| match mount {
                CurrentMount::Birth => CurrentMountImage::Birth,
                CurrentMount::Continue(lineage) => {
                    CurrentMountImage::Continue(lineage.durable_handle())
                }
            })
            .collect();
        let lineages = self
            .lineages
            .iter()
            .map(|lineage| LineageStateImage {
                handle: lineage.handle,
                parents: lineage.parents.clone(),
                claimed: lineage.claimed.load(Ordering::Acquire),
            })
            .collect();
        Ok(EnactedPopulationImage {
            enactment,
            active: (*self.active).clone(),
            event_surfaces: self.event_surfaces.clone(),
            emissions: self.emissions.clone(),
            currents,
            carried: self.carried.clone(),
            incidence_surface,
            directed_contacts: self.directed_contacts.clone(),
            prepared_cut: self.prepared_cut.as_ref().map(|prepared| PreparedCutImage {
                cut: prepared.cut,
                fold: prepared.fold.clone(),
                successor: (*prepared.successor).clone(),
            }),
            mounts,
            lineages,
        })
    }

    fn recovery_seed(
        image: EnactedPopulationImage,
    ) -> Result<EnactedRecoverySeed, ContactCycleError> {
        let active = Arc::new(image.active);
        let validated = active.validated()?;
        let expected_events = EventTopology::new_validated(validated)?.into_events();
        if expected_events != image.event_surfaces {
            return Err(ContactCycleError::RecoveryTopology);
        }
        image.emissions.validate_against(&active)?;
        let topology = ActiveTopology::new_validated(
            validated,
            &image.emissions,
            image.directed_contacts.clone(),
        )?;
        let (expected_carried, expected_incidence, expected_directed) = topology.into_owned_parts();
        let incidence_surface = image
            .incidence_surface
            .into_iter()
            .map(|surface| {
                usize::try_from(surface).map_err(|_| ContactCycleError::RecoveryTopology)
            })
            .collect::<Result<Vec<_>, _>>()?;
        if expected_carried != image.carried
            || expected_incidence != incidence_surface
            || expected_directed != image.directed_contacts
        {
            return Err(ContactCycleError::RecoveryTopology);
        }
        let currents = image
            .currents
            .into_iter()
            .map(CurrentOutcome::from_checkpoint_image)
            .collect::<Result<Vec<_>, _>>()?;
        if currents.len() != active.currents.len()
            || image.mounts.len() != currents.len()
            || image.lineages.len() != currents.len()
        {
            return Err(ContactCycleError::RecoveryTopology);
        }
        for (current, outcome) in currents.iter().enumerate() {
            let current = u64::try_from(current).map_err(|_| ContactCycleError::ResourceExtent)?;
            let span = active
                .currents
                .get(usize::try_from(current).map_err(|_| ContactCycleError::ResourceExtent)?)
                .ok_or(ContactCycleError::RecoveryTopology)?;
            if outcome.conduct.current != current
                || outcome.conduct.events != span.events()
                || outcome.contacts.iter().any(|contact| {
                    contact.event < span.event_offset()
                        || contact.event >= span.event_offset().saturating_add(span.events())
                })
            {
                return Err(ContactCycleError::RecoveryTopology);
            }
        }
        let prepared_cut = image
            .prepared_cut
            .map(|prepared| {
                if prepared.fold.cut() != prepared.cut {
                    return Err(ContactCycleError::RecoveryTopology);
                }
                Ok(PreparedCut {
                    cut: prepared.cut,
                    fold: prepared.fold,
                    successor: Arc::new(prepared.successor),
                })
            })
            .transpose()?;
        Ok(EnactedRecoverySeed {
            enactment: image.enactment,
            active,
            event_surfaces: image.event_surfaces,
            emissions: image.emissions,
            currents,
            carried: image.carried,
            incidence_surface,
            directed_contacts: image.directed_contacts,
            prepared_cut,
            mounts: image.mounts,
            lineages: image.lineages,
        })
    }

    pub fn active(&self) -> &Arc<ActiveCut> {
        &self.active
    }

    pub fn emissions(&self) -> &EmissionJournal {
        &self.emissions
    }

    /// Every source event stands once as its complete ordered relation-span face beside the one
    /// supplied action current.  This is enacted topology, not an observer reconstruction.
    pub fn event_surfaces(&self) -> &[EventSurface] {
        &self.event_surfaces
    }

    pub fn event_surface(&self, event: u64) -> Option<EventSurface> {
        self.event_surfaces
            .get(usize::try_from(event).ok()?)
            .copied()
    }

    pub fn event_atoms(&self, event: u64) -> Option<&[soma_abi::active::RelationAtom]> {
        let surface = self.event_surface(event)?;
        let first = usize::try_from(surface.atom_offset()).ok()?;
        let after = usize::try_from(surface.atom_offset().checked_add(surface.atoms())?).ok()?;
        self.active.atoms.get(first..after)
    }

    pub fn currents(&self) -> &[CurrentOutcome] {
        &self.currents
    }

    pub fn carried(&self) -> &[CarriedSpanSurface] {
        &self.carried
    }

    pub fn surface_for_incidence(&self, incidence: u64) -> Option<&CarriedSpanSurface> {
        let surface = *self
            .incidence_surface
            .get(usize::try_from(incidence).ok()?)?;
        self.carried.get(surface)
    }

    pub(crate) fn incidence_surface_index(&self) -> &[usize] {
        &self.incidence_surface
    }

    /// Every source-supplied causal hand remains a physical occurrence. Each incidence endpoint is
    /// its complete ordered event section; no first/last event or Cartesian endpoint is selected.
    pub fn directed_contacts(&self) -> &[DirectedCutContact] {
        &self.directed_contacts
    }

    pub fn prepared_cut(&self, cut: u64) -> Option<&PreparedCut> {
        self.prepared_cut
            .as_ref()
            .filter(|prepared| prepared.cut == cut)
    }

    pub fn mounts(&self) -> &[CurrentMount] {
        &self.mounts
    }

    fn install_lineages(
        &mut self,
        ecology: EcologyId,
        enactment: u64,
        ancestry: Option<&[Vec<LineageHandle>]>,
    ) -> Result<(), ContactCycleError> {
        if !self.lineages.is_empty() {
            return Err(ContactCycleError::RecoveryDuplicate);
        }
        if ancestry.is_some_and(|rows| rows.len() != self.currents.len()) {
            return Err(ContactCycleError::SettlementReturnExtent {
                expected: u64::try_from(self.currents.len())
                    .map_err(|_| ContactCycleError::ResourceExtent)?,
                actual: u64::try_from(ancestry.map_or(0, |rows| rows.len()))
                    .map_err(|_| ContactCycleError::ResourceExtent)?,
            });
        }
        let mut lineages = Vec::new();
        lineages
            .try_reserve_exact(self.currents.len())
            .map_err(|_| ContactCycleError::ResourceReservation)?;
        for (current_index, outcome) in self.currents.iter().enumerate() {
            let current =
                u64::try_from(current_index).map_err(|_| ContactCycleError::ResourceExtent)?;
            let handle = LineageHandle {
                ecology,
                enactment,
                current,
            };
            let mut parents = match ancestry {
                Some(rows) => rows[current_index].clone(),
                None => match self.mounts.get(current_index) {
                    Some(CurrentMount::Birth) => Default::default(),
                    Some(CurrentMount::Continue(lineage)) => {
                        vec![lineage.durable_handle()]
                    }
                    None => return Err(ContactCycleError::CurrentMountExtent),
                },
            };
            parents.sort_unstable();
            // Equal handles are lawful physical multiplicity: distinct event-incidence rows can
            // carry the same parent into one returned current.  Their exact rows remain in the
            // Holon settlement population; the lineage-side list preserves the same multiplicity
            // rather than silently quotienting it into a set.
            if parents
                .iter()
                .any(|parent| parent.ecology != ecology || *parent >= handle)
            {
                return Err(ContactCycleError::RecoveryDuplicate);
            }
            lineages.push(Arc::new(LineageState {
                handle,
                carrier: outcome.carrier.clone(),
                parents,
                claimed: AtomicBool::new(false),
            }));
        }
        self.lineages = lineages;
        Ok(())
    }

    fn prepare_cut(
        &mut self,
        cut: u64,
        standing: &SparseStandingSurface,
    ) -> Result<(), ContactCycleError> {
        if let Some(prepared) = &self.prepared_cut {
            return if prepared.cut == cut {
                Ok(())
            } else {
                Err(ContactCycleError::CutAbsent(cut))
            };
        }
        let fold = prepare_sparse_fold_from_owned(
            &self.active,
            &self.carried,
            &self.incidence_surface,
            &self.directed_contacts,
            cut,
            standing,
        )?;
        let successor = standing.prepare_successor(&fold)?;
        self.prepared_cut = Some(PreparedCut {
            cut,
            fold,
            successor: Arc::new(successor),
        });
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct IncomingDirectedContact {
    event: u64,
    contact: usize,
}

fn event_section_node(events: &[EventSurface]) -> Result<Node, ContactCycleError> {
    let mut node = events
        .first()
        .copied()
        .ok_or(ContactCycleError::ResourceExtent)?
        .node();
    for event in &events[1..] {
        let next = event.node();
        node = Node {
            well: node.well.mul(next.well),
            place: compose_place(node, next),
            len: node
                .len
                .checked_add(next.len)
                .ok_or(ContactCycleError::ResourceExtent)?,
        };
    }
    Ok(node)
}

fn prepare_directed_contacts(
    active: &ActiveCut,
    events: &EventTopology<'_>,
) -> Result<(Vec<DirectedCutContact>, Vec<IncomingDirectedContact>), ContactCycleError> {
    let directed_extent =
        usize::try_from(active.header.directed()).map_err(|_| ContactCycleError::ResourceExtent)?;
    let mut contacts = Vec::new();
    contacts
        .try_reserve_exact(directed_extent)
        .map_err(|_| ContactCycleError::ResourceReservation)?;
    let mut incoming = Vec::new();
    incoming
        .try_reserve_exact(directed_extent)
        .map_err(|_| ContactCycleError::ResourceReservation)?;

    let mut cut = 0u64;
    while cut < active.header.cuts() {
        let cut_span = active.cuts[cut as usize];
        for (local, surface) in events.directed(cut)?.into_iter().enumerate() {
            let directed = cut_span
                .directed_offset()
                .checked_add(u64::try_from(local).map_err(|_| ContactCycleError::ResourceExtent)?)
                .ok_or(ContactCycleError::ResourceExtent)?;
            let from = surface.from();
            let to = surface.to();
            let from_node = event_section_node(events.incidence_events(from)?)?;
            let to_node = event_section_node(events.incidence_events(to)?)?;
            let contact = contacts.len();
            contacts.push(DirectedCutContact::exact_sections(
                cut,
                directed,
                surface.edge(),
                from.event_offset(),
                to.event_offset(),
                from_node.place,
                to_node.place,
            ));
            // The receiver is captured before the complete target section begins. The endpoint is
            // the whole composed section; this ordinal only locates its lived receiving boundary.
            incoming.push(IncomingDirectedContact {
                event: to.event_offset(),
                contact,
            });
        }
        cut += 1;
    }
    if contacts.len() != directed_extent {
        return Err(ContactCycleError::ResourceExtent);
    }
    // This index only locates actual incoming rows at the target event. The source-directed
    // ordinal remains the secondary key, so it cannot choose, suppress, or manufacture contact.
    incoming.sort_unstable_by_key(|row| (row.event, row.contact));
    Ok((contacts, incoming))
}

pub struct PreparedContact {
    generation: u64,
    enacted: EnactedPopulation,
}

/// Handle for one world interval whose before, meeting, and deed roles have lived while its
/// consequence has not yet returned.  It is an address into the live Holon, not a scheduler token.
#[derive(Clone)]
pub struct OpenContact {
    transition: TransitionId,
    owner: Arc<EcologyOwner>,
    deed: Arc<EnactedPopulation>,
    deed_cut: u64,
}

impl OpenContact {
    pub fn transition(&self) -> TransitionId {
        self.transition
    }

    pub fn lineage(&self, current: u64) -> Option<LineageRef> {
        let current = usize::try_from(current).ok()?;
        let state = self.deed.lineages.get(current)?.clone();
        Some(LineageRef {
            owner: self.owner.clone(),
            state,
        })
    }

    pub fn carried_cut(&self) -> CarriedCutRef {
        CarriedCutRef {
            owner: self.owner.clone(),
            enacted: self.deed.clone(),
            cut: self.deed_cut,
        }
    }

    /// Exact birth/continuation mounts which formed this source deed. Recovery uses these live
    /// capabilities to rebind an already-contacted frontier without presenting the source again.
    pub fn source_mounts(&self) -> &[CurrentMount] {
        self.deed.mounts()
    }

    pub fn current_contact_state(&self, current: u64) -> Option<CurrentContactState> {
        self.carried_cut().current_contact_state(current)
    }
}

/// Receipt returned when an organ consequence has crossed the same mouth and the successor body
/// stands.  The receipt itself remains owned by `LiveHolon`; this handle locates its returned
/// enacted population in the active ecology.
#[derive(Clone)]
pub struct ClosedContact {
    transition: TransitionId,
    receipt: TransitionReceipt,
    owner: Arc<EcologyOwner>,
    source: Arc<EnactedPopulation>,
    source_cut: u64,
    returned: Arc<EnactedPopulation>,
    return_cut: u64,
}

/// A returned population whose phase-five settlement has committed while the successor has not
/// yet been installed as the Holon's after role. This capability is recoverable and closes without
/// replaying source conduct, world action, or return conduct.
#[derive(Clone)]
pub struct PendingAfterContact {
    transition: TransitionId,
    owner: Arc<EcologyOwner>,
    source: Arc<EnactedPopulation>,
    source_cut: u64,
    returned: Arc<EnactedPopulation>,
    return_cut: u64,
    after: Arc<SparseStandingSurface>,
}

impl PendingAfterContact {
    pub fn transition(&self) -> TransitionId {
        self.transition
    }
}

impl ClosedContact {
    pub fn transition(&self) -> TransitionId {
        self.transition
    }

    /// Compact six-role testimony copied at the moment of closure. It remains valid even after
    /// completed live surface owners are later dissipated from resident memory.
    pub fn receipt(&self) -> TransitionReceipt {
        self.receipt
    }

    pub fn lineage(&self, current: u64) -> Option<LineageRef> {
        let current = usize::try_from(current).ok()?;
        let state = self.returned.lineages.get(current)?.clone();
        Some(LineageRef {
            owner: self.owner.clone(),
            state,
        })
    }

    pub fn source_lineage(&self, current: u64) -> Option<LineageRef> {
        let current = usize::try_from(current).ok()?;
        let state = self.source.lineages.get(current)?.clone();
        Some(LineageRef {
            owner: self.owner.clone(),
            state,
        })
    }

    pub fn source_carried_cut(&self) -> CarriedCutRef {
        CarriedCutRef {
            owner: self.owner.clone(),
            enacted: self.source.clone(),
            cut: self.source_cut,
        }
    }

    pub fn source_mounts(&self) -> &[CurrentMount] {
        self.source.mounts()
    }

    pub fn carried_cut(&self) -> CarriedCutRef {
        CarriedCutRef {
            owner: self.owner.clone(),
            enacted: self.returned.clone(),
            cut: self.return_cut,
        }
    }
}

/// Terminal source contact for which no world-side relation crossed. The deed and its post-deed
/// receiver are real; consequence and return remain absent. Every source lineage remains live and
/// can be continued by a genuinely later event.
#[derive(Clone)]
pub struct SilentContact {
    transition: TransitionId,
    receipt: SilentReceipt,
    owner: Arc<EcologyOwner>,
    source: Arc<EnactedPopulation>,
    source_cut: u64,
}

impl SilentContact {
    pub fn transition(&self) -> TransitionId {
        self.transition
    }

    pub fn receipt(&self) -> SilentReceipt {
        self.receipt
    }

    pub fn lineage(&self, current: u64) -> Option<LineageRef> {
        let current = usize::try_from(current).ok()?;
        let state = self.source.lineages.get(current)?.clone();
        Some(LineageRef {
            owner: self.owner.clone(),
            state,
        })
    }

    pub fn carried_cut(&self) -> CarriedCutRef {
        CarriedCutRef {
            owner: self.owner.clone(),
            enacted: self.source.clone(),
            cut: self.source_cut,
        }
    }

    pub fn source_mounts(&self) -> &[CurrentMount] {
        self.source.mounts()
    }
}

/// One exact transition capability rebound from a complete ecology checkpoint.  No variant
/// reenacts contact or world law; it only restores the capability matching the Holon's committed
/// phase.
pub enum TransitionContact {
    Open(OpenContact),
    Returned(ClosedContact),
    Silent(SilentContact),
}

/// In-memory active ecology.  This owner contains no filesystem, text, modality, semantic index,
/// target score, or scheduler.  Material organs construct `ActiveCut`; the ecology only conducts
/// that topology and installs an exact supplied cut.
pub struct LiveEcology {
    owner: Arc<EcologyOwner>,
    generation: u64,
    next_enactment: u64,
    standing: Arc<SparseStandingSurface>,
    enacted: Vec<Arc<EnactedPopulation>>,
    holon: LiveHolon,
    lineages: Vec<Arc<LineageState>>,
}

impl LiveEcology {
    pub fn new(id: EcologyId, standing: SparseStandingSurface) -> Self {
        Self {
            owner: Arc::new(EcologyOwner { id }),
            generation: 0,
            next_enactment: 0,
            standing: Arc::new(standing),
            enacted: Vec::new(),
            holon: LiveHolon::new(),
            lineages: Vec::new(),
        }
    }

    pub fn id(&self) -> EcologyId {
        self.owner.id
    }

    /// Resolve one stable lineage address in this already-live ecology.  This locates exact
    /// carried state; it does not claim, schedule, or select the lineage.
    pub fn lineage(&self, handle: LineageHandle) -> Option<LineageRef> {
        if handle.ecology != self.owner.id {
            return None;
        }
        let at = self
            .lineages
            .binary_search_by_key(&handle, |state| state.handle)
            .ok()?;
        let state = self.lineages[at].clone();
        if state.claimed.load(Ordering::Acquire) {
            return None;
        }
        Some(LineageRef {
            owner: self.owner.clone(),
            state,
        })
    }

    /// Capture the complete committed ecology at any lifecycle phase. Unlike `rest_image`, this
    /// retains enacted populations and the live Holon, including an open world interval. The
    /// resulting typed graph is testimony only and is never submitted to the active mouth.
    pub fn checkpoint(&self) -> Result<EcologyCheckpoint, ContactCycleError> {
        let enacted = self
            .enacted
            .iter()
            .map(|population| population.checkpoint_image())
            .collect::<Result<Vec<_>, _>>()?;
        Ok(EcologyCheckpoint {
            version: ECOLOGY_CHECKPOINT_VERSION,
            id: self.owner.id,
            generation: self.generation,
            next_enactment: self.next_enactment,
            standing: (*self.standing).clone(),
            holon: self.holon.checkpoint_image(&self.enacted)?,
            enacted,
        })
    }

    /// Rebind a complete typed checkpoint without replaying source conduct, world action, return
    /// conduct, or settlement. Every durable handle regains one canonical `Arc`; equal parent rows
    /// and equal-valued surface occurrences remain plural.
    pub fn from_checkpoint(image: EcologyCheckpoint) -> Result<Self, ContactCycleError> {
        if image.version != ECOLOGY_CHECKPOINT_VERSION {
            return Err(ContactCycleError::RecoveryVersion);
        }
        let owner = Arc::new(EcologyOwner { id: image.id });
        let seeds = image
            .enacted
            .into_iter()
            .map(EnactedPopulation::recovery_seed)
            .collect::<Result<Vec<_>, _>>()?;
        let mut previous_enactment = None;
        let mut all_lineages = Vec::new();
        let lineage_extent = seeds
            .iter()
            .try_fold(0usize, |extent, seed| {
                extent.checked_add(seed.lineages.len())
            })
            .ok_or(ContactCycleError::ResourceExtent)?;
        all_lineages
            .try_reserve_exact(lineage_extent)
            .map_err(|_| ContactCycleError::ResourceReservation)?;
        for seed in &seeds {
            if previous_enactment.is_some_and(|previous| previous >= seed.enactment)
                || seed.enactment >= image.next_enactment
                || seed.lineages.len() != seed.currents.len()
            {
                return Err(ContactCycleError::RecoveryDuplicate);
            }
            for (current, lineage) in seed.lineages.iter().enumerate() {
                let current_at = current;
                let current =
                    u64::try_from(current_at).map_err(|_| ContactCycleError::ResourceExtent)?;
                let expected = LineageHandle {
                    ecology: image.id,
                    enactment: seed.enactment,
                    current,
                };
                if lineage.handle != expected
                    || lineage
                        .parents
                        .iter()
                        .any(|parent| parent.ecology != image.id || *parent >= expected)
                    || lineage.parents.windows(2).any(|pair| pair[0] > pair[1])
                {
                    return Err(ContactCycleError::RecoveryDuplicate);
                }
                all_lineages.push(Arc::new(LineageState {
                    handle: expected,
                    carrier: seed.currents[current_at].carrier.clone(),
                    parents: lineage.parents.clone(),
                    claimed: AtomicBool::new(lineage.claimed),
                }));
            }
            previous_enactment = Some(seed.enactment);
        }
        for state in &all_lineages {
            if state.parents.iter().any(|parent| {
                all_lineages
                    .binary_search_by_key(parent, |candidate| candidate.handle)
                    .is_err()
            }) {
                return Err(ContactCycleError::RecoveryIdentity);
            }
        }

        let resolve = |handle: LineageHandle| {
            all_lineages
                .binary_search_by_key(&handle, |state| state.handle)
                .ok()
                .and_then(|at| all_lineages.get(at).cloned())
        };
        let mut mounted = Vec::new();
        let mut enacted = Vec::new();
        enacted
            .try_reserve_exact(seeds.len())
            .map_err(|_| ContactCycleError::ResourceReservation)?;
        for seed in seeds {
            let mut mounts = Vec::new();
            mounts
                .try_reserve_exact(seed.mounts.len())
                .map_err(|_| ContactCycleError::ResourceReservation)?;
            for mount in seed.mounts {
                mounts.push(match mount {
                    CurrentMountImage::Birth => CurrentMount::Birth,
                    CurrentMountImage::Continue(handle) => {
                        if mounted.contains(&handle) {
                            return Err(ContactCycleError::RecoveryDuplicate);
                        }
                        let state = resolve(handle).ok_or(ContactCycleError::RecoveryIdentity)?;
                        if !state.claimed.load(Ordering::Acquire)
                            || handle.enactment >= seed.enactment
                        {
                            return Err(ContactCycleError::RecoveryIdentity);
                        }
                        mounted.push(handle);
                        CurrentMount::Continue(LineageRef {
                            owner: owner.clone(),
                            state,
                        })
                    }
                });
            }
            let lineages = seed
                .lineages
                .iter()
                .map(|lineage| resolve(lineage.handle).ok_or(ContactCycleError::RecoveryIdentity))
                .collect::<Result<Vec<_>, _>>()?;
            for (current, lineage) in lineages.iter().enumerate() {
                if !Arc::ptr_eq(&lineage.carrier, &seed.currents[current].carrier) {
                    return Err(ContactCycleError::RecoveryIdentity);
                }
                if let Some(CurrentMount::Continue(parent)) = mounts.get(current) {
                    if !lineage.parents.contains(&parent.durable_handle()) {
                        return Err(ContactCycleError::RecoveryIdentity);
                    }
                }
            }
            enacted.push(Arc::new(EnactedPopulation {
                active: seed.active,
                event_surfaces: seed.event_surfaces,
                emissions: seed.emissions,
                currents: seed.currents,
                carried: seed.carried,
                incidence_surface: seed.incidence_surface,
                directed_contacts: seed.directed_contacts,
                prepared_cut: seed.prepared_cut,
                mounts,
                lineages,
            }));
        }
        let standing = if let Some(last) = enacted.last() {
            let successor = last
                .prepared_cut
                .as_ref()
                .ok_or(ContactCycleError::RecoveryTopology)?
                .successor
                .clone();
            if successor.as_ref() != &image.standing {
                return Err(ContactCycleError::RecoveryTopology);
            }
            successor
        } else {
            Arc::new(image.standing.clone())
        };
        let holon = LiveHolon::from_checkpoint_image(image.holon, &enacted)?;
        let lineages = all_lineages
            .into_iter()
            .filter(|state| !state.claimed.load(Ordering::Acquire))
            .collect();
        Ok(Self {
            owner,
            generation: image.generation,
            next_enactment: image.next_enactment,
            standing,
            enacted,
            holon,
            lineages,
        })
    }

    /// Capture the exact live rest frontier. This refuses an open Holon; a pending world interval
    /// must retain its `OpenContact` rather than masquerading as quiescence.
    pub fn rest_image(&self) -> Result<EcologyRestImage, ContactCycleError> {
        if self.holon.open_transitions() != 0 {
            return Err(ContactCycleError::LiveInterval);
        }
        let mut lineages = Vec::new();
        lineages
            .try_reserve_exact(self.lineages.len())
            .map_err(|_| ContactCycleError::ResourceReservation)?;
        for state in &self.lineages {
            if !state.claimed.load(Ordering::Acquire) {
                lineages.push(state.image()?);
            }
        }
        Ok(EcologyRestImage {
            id: self.owner.id,
            generation: self.generation,
            next_enactment: self.next_enactment,
            standing: (*self.standing).clone(),
            lineages,
        })
    }

    /// Reopen one exact rest image. Carrier words are validated as typed continuation testimony;
    /// neither they nor the standing snapshot are presented as a new active current.
    pub fn from_rest_image(image: EcologyRestImage) -> Result<Self, ContactCycleError> {
        let owner = Arc::new(EcologyOwner { id: image.id });
        let mut lineages = Vec::new();
        lineages
            .try_reserve_exact(image.lineages.len())
            .map_err(|_| ContactCycleError::ResourceReservation)?;
        let mut previous = None;
        for lineage in image.lineages {
            if lineage.handle.ecology != image.id {
                return Err(ContactCycleError::RecoveryIdentity);
            }
            if previous.is_some_and(|handle| handle >= lineage.handle) {
                return Err(ContactCycleError::RecoveryDuplicate);
            }
            let carrier = Arc::new(
                LiveCarrierSnapshot::from_native_words(&lineage.native_carrier)
                    .map_err(|_| ContactCycleError::RecoveryCarrier)?,
            );
            if lineage
                .parents
                .iter()
                .any(|parent| parent.ecology != image.id || *parent >= lineage.handle)
                || lineage.parents.windows(2).any(|pair| pair[0] > pair[1])
            {
                return Err(ContactCycleError::RecoveryDuplicate);
            }
            let state = Arc::new(LineageState {
                handle: lineage.handle,
                carrier,
                parents: lineage.parents,
                claimed: AtomicBool::new(false),
            });
            previous = Some(lineage.handle);
            lineages.push(state);
        }
        Ok(Self {
            owner,
            generation: image.generation,
            next_enactment: image.next_enactment,
            standing: Arc::new(image.standing),
            enacted: Vec::new(),
            holon: LiveHolon::new(),
            lineages,
        })
    }

    pub fn standing(&self) -> &SparseStandingSurface {
        &self.standing
    }

    pub fn generation(&self) -> u64 {
        self.generation
    }

    pub fn enacted(&self) -> &[Arc<EnactedPopulation>] {
        &self.enacted
    }

    pub fn holon(&self) -> &LiveHolon {
        &self.holon
    }

    /// Rebind one already-open interval after exact recovery. This locates the committed source
    /// deed; it does not replay preparation or contact.
    pub fn open_contact(&self, transition: TransitionId) -> Result<OpenContact, ContactCycleError> {
        let (deed, deed_cut) = self.holon.open_deed(transition)?;
        if !self
            .enacted
            .iter()
            .any(|candidate| Arc::ptr_eq(candidate, &deed))
        {
            return Err(ContactCycleError::RecoveryIdentity);
        }
        Ok(OpenContact {
            transition,
            owner: self.owner.clone(),
            deed,
            deed_cut,
        })
    }

    fn enacted_at_holon_cut(
        &self,
        ordinal: u64,
    ) -> Result<(Arc<EnactedPopulation>, u64), ContactCycleError> {
        let cut = self.holon.boundary_cut(ordinal)?;
        let enacted = self
            .holon
            .surface(cut.surface())?
            .enacted()
            .cloned()
            .ok_or(ContactCycleError::RecoveryTopology)?;
        if !self
            .enacted
            .iter()
            .any(|candidate| Arc::ptr_eq(candidate, &enacted))
        {
            return Err(ContactCycleError::RecoveryIdentity);
        }
        Ok((enacted, cut.cut()))
    }

    /// Recover the exact capability already committed for one interval.  Open returns remain
    /// open; a completed return or silence is reconstructed from the live Holon rather than from
    /// an organ's copy of its prior world material.
    pub fn transition_contact(
        &self,
        transition: TransitionId,
    ) -> Result<TransitionContact, ContactCycleError> {
        match self.holon.transition_status(transition)? {
            crate::TransitionStatus::Open(_) => {
                self.open_contact(transition).map(TransitionContact::Open)
            }
            crate::TransitionStatus::Returned => {
                let receipt = self.holon.receipt(transition)?;
                let (source, source_cut) = self.enacted_at_holon_cut(receipt.deed_cut())?;
                let (returned, return_cut) = self.enacted_at_holon_cut(receipt.return_cut())?;
                Ok(TransitionContact::Returned(ClosedContact {
                    transition,
                    receipt,
                    owner: self.owner.clone(),
                    source,
                    source_cut,
                    returned,
                    return_cut,
                }))
            }
            crate::TransitionStatus::Silent => {
                let receipt = self.holon.silent_receipt(transition)?;
                let (source, source_cut) = self.enacted_at_holon_cut(receipt.deed_cut())?;
                Ok(TransitionContact::Silent(SilentContact {
                    transition,
                    receipt,
                    owner: self.owner.clone(),
                    source,
                    source_cut,
                }))
            }
        }
    }

    /// Recover only the exact source deed for any committed transition state. This is used to
    /// rebuild listener-side frontier incidence after closure; attempting to close it again still
    /// meets the Holon's ordinary closed-transition refusal.
    pub fn source_contact(
        &self,
        transition: TransitionId,
    ) -> Result<OpenContact, ContactCycleError> {
        let (deed, deed_cut) = match self.holon.transition_status(transition)? {
            crate::TransitionStatus::Open(_) => self.holon.open_deed(transition)?,
            crate::TransitionStatus::Returned => {
                let receipt = self.holon.receipt(transition)?;
                self.enacted_at_holon_cut(receipt.deed_cut())?
            }
            crate::TransitionStatus::Silent => {
                let receipt = self.holon.silent_receipt(transition)?;
                self.enacted_at_holon_cut(receipt.deed_cut())?
            }
        };
        Ok(OpenContact {
            transition,
            owner: self.owner.clone(),
            deed,
            deed_cut,
        })
    }

    /// Verify that a recovered frontier's complete settlement population is the population the
    /// live Holon actually closed. This compares typed rows and never reconstructs a decision from
    /// a receipt scalar.
    pub fn settlement_matches(
        &self,
        transition: TransitionId,
        plan: &SettlementPlan,
    ) -> Result<bool, ContactCycleError> {
        let (sources, origins, lineages) = plan.abi_populations()?;
        let (actual_sources, actual_origins, actual_lineages) =
            self.holon.settlement_populations(transition)?;
        Ok(actual_sources == sources && actual_origins == origins && actual_lineages == lineages)
    }

    /// Compare a world return checkpoint with the exact consequence and returned surfaces already
    /// committed in this Holon. Value equality validates testimony; the live ecology continues to
    /// own the canonical occurrences and their shared identities.
    pub fn world_return_matches(
        &self,
        transition: TransitionId,
        consequence: &ActiveCut,
        consequence_cut: u64,
        returned: &ActiveCut,
        return_cut: u64,
    ) -> Result<bool, ContactCycleError> {
        let consequence_role = self.holon.transition_role_cut(transition, 3)?;
        let returned_role = self.holon.transition_role_cut(transition, 4)?;
        let mounted_consequence = self
            .holon
            .surface(consequence_role.surface())?
            .active()
            .ok_or(ContactCycleError::RecoveryTopology)?;
        let mounted_return = self
            .holon
            .surface(returned_role.surface())?
            .enacted()
            .ok_or(ContactCycleError::RecoveryTopology)?;
        Ok(consequence_role.cut() == consequence_cut
            && returned_role.cut() == return_cut
            && mounted_consequence.as_ref() == consequence
            && mounted_return.active().as_ref() == returned)
    }

    pub fn prepare(&self, active: Arc<ActiveCut>) -> Result<PreparedContact, ContactCycleError> {
        let currents = active.header.currents();
        let mounts = birth_mounts(currents)?;
        prepare_host_with_order(active, &self.standing, self.generation, mounts, 0..currents)
    }

    /// Conduct a cut whose current-local bodies are either genuinely born or explicitly continued
    /// by world-supplied live incidence.  Position in `mounts` is the active current ordinal; a
    /// missing entry births, while a carried entry remounts that exact current.  No provenance or
    /// material content is consulted to choose between them.
    pub fn prepare_mounted(
        &self,
        active: Arc<ActiveCut>,
        mounts: &[CurrentMount],
    ) -> Result<PreparedContact, ContactCycleError> {
        let currents = active.header.currents();
        if u64::try_from(mounts.len()).ok() != Some(currents) {
            return Err(ContactCycleError::CurrentMountExtent);
        }
        self.validate_mounts(mounts)?;
        prepare_host_with_order(
            active,
            &self.standing,
            self.generation,
            mounts.to_vec(),
            0..currents,
        )
    }

    fn validate_mounts(&self, mounts: &[CurrentMount]) -> Result<(), ContactCycleError> {
        for (ordinal, mount) in mounts.iter().enumerate() {
            let CurrentMount::Continue(lineage) = mount else {
                continue;
            };
            let ordinal = ordinal as u64;
            if !Arc::ptr_eq(&lineage.owner, &self.owner) {
                return Err(ContactCycleError::ForeignLineage(ordinal));
            }
            if lineage.state.claimed.load(Ordering::Acquire) {
                return Err(ContactCycleError::LineageClaimed(ordinal));
            }
            for earlier in &mounts[..ordinal as usize] {
                if let CurrentMount::Continue(earlier) = earlier {
                    if Arc::ptr_eq(&earlier.state, &lineage.state) {
                        return Err(ContactCycleError::DuplicateLineage(ordinal));
                    }
                }
            }
        }
        Ok(())
    }

    fn preflight_claims(&mut self, mounts: &[CurrentMount]) -> Result<(), ContactCycleError> {
        self.validate_mounts(mounts)
    }

    fn validate_live_lineage(
        &self,
        current: u64,
        lineage: &LineageRef,
    ) -> Result<(), ContactCycleError> {
        if !Arc::ptr_eq(&lineage.owner, &self.owner) {
            return Err(ContactCycleError::ForeignLineage(current));
        }
        if lineage.state.claimed.load(Ordering::Acquire) {
            return Err(ContactCycleError::LineageClaimed(current));
        }
        let at = self
            .lineages
            .binary_search_by_key(&lineage.state.handle, |state| state.handle)
            .map_err(|_| ContactCycleError::LineageClaimed(current))?;
        if !Arc::ptr_eq(&self.lineages[at], &lineage.state) {
            return Err(ContactCycleError::ForeignLineage(current));
        }
        Ok(())
    }

    fn validate_ended(
        &self,
        ended: &[(u64, LineageRef)],
        mounts: &[CurrentMount],
    ) -> Result<(), ContactCycleError> {
        for (at, (current, lineage)) in ended.iter().enumerate() {
            self.validate_live_lineage(*current, lineage)?;
            if !Arc::ptr_eq(&lineage.owner, &self.owner) {
                return Err(ContactCycleError::ForeignLineage(*current));
            }
            if lineage.state.claimed.load(Ordering::Acquire) {
                return Err(ContactCycleError::LineageClaimed(*current));
            }
            if ended[..at]
                .iter()
                .any(|(_, earlier)| Arc::ptr_eq(&earlier.state, &lineage.state))
                || mounts.iter().any(|mount| {
                    matches!(mount, CurrentMount::Continue(mounted) if Arc::ptr_eq(&mounted.state, &lineage.state))
                })
            {
                return Err(ContactCycleError::DuplicateLineage(*current));
            }
        }
        Ok(())
    }

    fn install_claims(&mut self, mounts: &[CurrentMount]) {
        for mount in mounts {
            let CurrentMount::Continue(lineage) = mount else {
                continue;
            };
            lineage.state.claimed.store(true, Ordering::Release);
            if let Ok(at) = self
                .lineages
                .binary_search_by_key(&lineage.state.handle, |state| state.handle)
            {
                self.lineages.remove(at);
            }
        }
    }

    fn install_ended(&mut self, ended: &[(u64, LineageRef)]) {
        for (_, lineage) in ended {
            lineage.state.claimed.store(true, Ordering::Release);
            if let Ok(at) = self
                .lineages
                .binary_search_by_key(&lineage.state.handle, |state| state.handle)
            {
                self.lineages.remove(at);
            }
        }
    }

    fn preflight_new_lineages(
        &mut self,
        enacted: &Arc<EnactedPopulation>,
    ) -> Result<(), ContactCycleError> {
        self.lineages
            .try_reserve_exact(enacted.lineages.len())
            .map_err(|_| ContactCycleError::ResourceReservation)?;
        for state in &enacted.lineages {
            if self
                .lineages
                .last()
                .is_some_and(|previous| previous.handle >= state.handle)
            {
                return Err(ContactCycleError::RecoveryDuplicate);
            }
        }
        Ok(())
    }

    fn install_new_lineages(&mut self, enacted: &Arc<EnactedPopulation>) {
        self.lineages.extend(enacted.lineages.iter().cloned());
    }

    fn validate_return_settlement(
        &self,
        open: &OpenContact,
        returned: &EnactedPopulation,
        plan: &SettlementPlan,
    ) -> Result<(Vec<(u64, LineageRef)>, Vec<Vec<LineageHandle>>), ContactCycleError> {
        let source_currents = open.deed.active.header.currents();
        let source_actual =
            u64::try_from(plan.source.len()).map_err(|_| ContactCycleError::ResourceExtent)?;
        if source_actual != source_currents {
            return Err(ContactCycleError::SettlementSourceExtent {
                expected: source_currents,
                actual: source_actual,
            });
        }
        let returned_currents = returned.active.header.currents();
        let origins_actual =
            u64::try_from(plan.origins.len()).map_err(|_| ContactCycleError::ResourceExtent)?;
        if origins_actual != returned_currents {
            return Err(ContactCycleError::SettlementReturnExtent {
                expected: returned_currents,
                actual: origins_actual,
            });
        }

        let source_carried = open.carried_cut();
        let mut lineages = Vec::new();
        lineages
            .try_reserve_exact(plan.lineages.len())
            .map_err(|_| ContactCycleError::ResourceReservation)?;
        for row in plan.lineages.iter().copied() {
            let Some((source_current, _)) =
                source_carried.incidence_event(row.source_incidence(), row.source_event_offset())
            else {
                return Err(ContactCycleError::SettlementLineageOutOfRange {
                    source_incidence: row.source_incidence(),
                    source_event_offset: row.source_event_offset(),
                    returned_incidence: row.returned_incidence(),
                    returned_event_offset: row.returned_event_offset(),
                });
            };
            let Some((returned_current, _)) = cut_incidence_event(
                returned.active(),
                returned
                    .prepared_cut
                    .as_ref()
                    .ok_or(ContactCycleError::ResourceExtent)?
                    .cut,
                row.returned_incidence(),
                row.returned_event_offset(),
            ) else {
                return Err(ContactCycleError::SettlementLineageOutOfRange {
                    source_incidence: row.source_incidence(),
                    source_event_offset: row.source_event_offset(),
                    returned_incidence: row.returned_incidence(),
                    returned_event_offset: row.returned_event_offset(),
                });
            };
            if !source_carried
                .incidence_event_contacted(row.source_incidence(), row.source_event_offset())
                .unwrap_or(false)
            {
                return Err(ContactCycleError::SettlementLineageNotContacted {
                    source_incidence: row.source_incidence(),
                    source_event_offset: row.source_event_offset(),
                });
            }
            lineages.push(ResolvedLineageIncidence {
                source_current,
                returned_current,
            });
        }

        let returned_extent =
            usize::try_from(returned_currents).map_err(|_| ContactCycleError::ResourceExtent)?;
        let mut continued_targets = Vec::new();
        continued_targets
            .try_reserve_exact(returned_extent)
            .map_err(|_| ContactCycleError::ResourceReservation)?;
        continued_targets.resize(returned_extent, None);
        let mut ended = Vec::new();
        ended
            .try_reserve_exact(plan.source.len())
            .map_err(|_| ContactCycleError::ResourceReservation)?;

        for (source_index, disposition) in plan.source.iter().copied().enumerate() {
            let source_current =
                u64::try_from(source_index).map_err(|_| ContactCycleError::ResourceExtent)?;
            let state = open
                .current_contact_state(source_current)
                .ok_or(ContactCycleError::ResourceExtent)?;
            if state.unresolved() {
                return Err(ContactCycleError::SettlementUnresolved(source_current));
            }
            let outgoing = lineages
                .iter()
                .filter(|lineage| lineage.source_current == source_current)
                .count();
            if !state.contacted() {
                if disposition != SourceDisposition::Standing || outgoing != 0 {
                    return Err(ContactCycleError::SettlementContact(source_current));
                }
                let lineage = open
                    .lineage(source_current)
                    .ok_or(ContactCycleError::LineageAbsent(source_current))?;
                self.validate_live_lineage(source_current, &lineage)?;
                continue;
            }
            match disposition {
                SourceDisposition::Standing => {
                    if outgoing == 0 {
                        return Err(ContactCycleError::SettlementContact(source_current));
                    }
                    let lineage = open
                        .lineage(source_current)
                        .ok_or(ContactCycleError::LineageAbsent(source_current))?;
                    self.validate_live_lineage(source_current, &lineage)?;
                }
                SourceDisposition::Ended => ended.push((
                    source_current,
                    open.lineage(source_current)
                        .ok_or(ContactCycleError::LineageAbsent(source_current))?,
                )),
                SourceDisposition::Continued(returned_current) => {
                    if returned_current >= returned_currents {
                        return Err(ContactCycleError::SettlementReturnTarget(returned_current));
                    }
                    if !lineages.iter().any(|lineage| {
                        lineage.source_current == source_current
                            && lineage.returned_current == returned_current
                    }) {
                        return Err(ContactCycleError::SettlementLineageAbsent {
                            source_current,
                            returned_current,
                        });
                    }
                    let target = &mut continued_targets[returned_current as usize];
                    if target.replace(source_current).is_some() {
                        return Err(ContactCycleError::SettlementReturnTarget(returned_current));
                    }
                }
            }
        }

        let mut ancestry = Vec::new();
        ancestry
            .try_reserve_exact(returned_extent)
            .map_err(|_| ContactCycleError::ResourceReservation)?;
        ancestry.resize_with(returned_extent, Vec::new);
        for lineage in &lineages {
            ancestry[lineage.returned_current as usize].push(
                open.lineage(lineage.source_current)
                    .ok_or(ContactCycleError::LineageAbsent(lineage.source_current))?
                    .durable_handle(),
            );
        }

        for (returned_index, origin) in plan.origins.iter().copied().enumerate() {
            let returned_current =
                u64::try_from(returned_index).map_err(|_| ContactCycleError::ResourceExtent)?;
            let mount = returned
                .mounts
                .get(returned_index)
                .ok_or(ContactCycleError::CurrentMountExtent)?;
            match origin {
                ReturnOrigin::Birth => {
                    if continued_targets[returned_index].is_some()
                        || !matches!(mount, CurrentMount::Birth)
                        || ancestry[returned_index].is_empty()
                    {
                        return Err(ContactCycleError::SettlementReturnMount(returned_current));
                    }
                }
                ReturnOrigin::Continued(source_current) => {
                    let source_index = usize::try_from(source_current)
                        .map_err(|_| ContactCycleError::ResourceExtent)?;
                    if source_index >= plan.source.len()
                        || continued_targets[returned_index] != Some(source_current)
                        || plan.source[source_index]
                            != SourceDisposition::Continued(returned_current)
                        || !lineages.iter().any(|lineage| {
                            lineage.source_current == source_current
                                && lineage.returned_current == returned_current
                        })
                    {
                        return Err(ContactCycleError::SettlementReturnOrigin(returned_current));
                    }
                    let expected = open
                        .lineage(source_current)
                        .ok_or(ContactCycleError::LineageAbsent(source_current))?
                        .durable_handle();
                    if !matches!(
                        mount,
                        CurrentMount::Continue(lineage)
                            if lineage.durable_handle() == expected
                    ) {
                        return Err(ContactCycleError::SettlementReturnMount(returned_current));
                    }
                }
            }
            // Preserve repeated event-level incidence. Equal parent handles can stand more than
            // once because their distinct rows remain in the Holon settlement population.
        }
        Ok((ended, ancestry))
    }

    /// Install the successor belonging to one actual world-supplied cut.  The ordinal is not a
    /// preference: it names the boundary that genuinely closed outside Soma.
    pub fn commit(
        &mut self,
        mut prepared: PreparedContact,
        cut: u64,
    ) -> Result<OpenContact, ContactCycleError> {
        if prepared.generation != self.generation {
            return Err(ContactCycleError::ReceiverChanged);
        }
        let next_generation = self
            .generation
            .checked_add(1)
            .ok_or(ContactCycleError::ResourceExtent)?;
        prepared.enacted.prepare_cut(cut, &self.standing)?;
        let prepared_cut = prepared
            .enacted
            .prepared_cut(cut)
            .ok_or(ContactCycleError::CutAbsent(cut))?;
        let successor = prepared_cut.successor.clone();
        let enactment = self.next_enactment;
        let next_enactment = enactment
            .checked_add(1)
            .ok_or(ContactCycleError::ResourceExtent)?;
        prepared
            .enacted
            .install_lineages(self.owner.id, enactment, None)?;
        let enacted = Arc::new(prepared.enacted);
        self.enacted
            .try_reserve(1)
            .map_err(|_| ContactCycleError::ResourceReservation)?;
        self.preflight_claims(enacted.mounts())?;
        self.preflight_new_lineages(&enacted)?;
        // The Holon closes every validation/allocation boundary before its first append. After
        // this succeeds, the remaining owner moves and scalar assignments are infallible.
        let transition = self
            .holon
            .open_enacted(self.standing.clone(), enacted.clone(), cut)?;

        self.enacted.push(enacted.clone());
        self.install_claims(enacted.mounts());
        self.install_new_lineages(&enacted);
        self.standing = successor;
        self.generation = next_generation;
        self.next_enactment = next_enactment;
        Ok(OpenContact {
            transition,
            owner: self.owner.clone(),
            deed: enacted,
            deed_cut: cut,
        })
    }

    /// Close a real world interval. `returned` is the active cut exposed by the organ after its
    /// material consequence; it is conducted against the contemporary standing body before this
    /// call. `consequence_cut` names the organ's actual consequence face, while `return_cut` names
    /// the cut whose enactment becomes the returned role and the new standing receiver.
    pub fn close(
        &mut self,
        open: OpenContact,
        consequence: Arc<ActiveCut>,
        returned: PreparedContact,
        consequence_cut: u64,
        return_cut: u64,
    ) -> Result<ClosedContact, ContactCycleError> {
        let source_currents = open.deed.active.header.currents();
        let returned_currents = returned.enacted.active.header.currents();
        if source_currents != returned_currents {
            return Err(ContactCycleError::SettlementReturnExtent {
                expected: source_currents,
                actual: returned_currents,
            });
        }
        let source_carried = open.carried_cut();
        let mut lineages = Vec::new();
        lineages
            .try_reserve_exact(
                usize::try_from(source_currents).map_err(|_| ContactCycleError::ResourceExtent)?,
            )
            .map_err(|_| ContactCycleError::ResourceReservation)?;
        for current in 0..source_currents {
            let source_cut = open.deed.active.cuts[open.deed_cut as usize];
            let mut source_occurrence = None;
            for local in 0..source_cut.incidences() {
                let incidence =
                    open.deed.active.incidences[(source_cut.incidence_offset() + local) as usize];
                if incidence.current() != current {
                    continue;
                }
                for event in 0..incidence.current_events() {
                    if source_carried
                        .incidence_event_contacted(local, event)
                        .unwrap_or(false)
                    {
                        source_occurrence = Some((local, event));
                        break;
                    }
                }
                if source_occurrence.is_some() {
                    break;
                }
            }
            let returned_cut = returned.enacted.active.cuts[return_cut as usize];
            let mut returned_occurrence = None;
            for local in 0..returned_cut.incidences() {
                let incidence = returned.enacted.active.incidences
                    [(returned_cut.incidence_offset() + local) as usize];
                if incidence.current() == current {
                    returned_occurrence = Some((local, 0));
                    break;
                }
            }
            if let (
                Some((source_incidence, source_event)),
                Some((returned_incidence, returned_event)),
            ) = (source_occurrence, returned_occurrence)
            {
                lineages.push(LineageIncidence::new(
                    source_incidence,
                    source_event,
                    returned_incidence,
                    returned_event,
                ));
            }
        }
        let plan = SettlementPlan::new(
            (0..source_currents)
                .map(SourceDisposition::Continued)
                .collect(),
            (0..source_currents).map(ReturnOrigin::Continued).collect(),
            lineages,
        );
        self.close_resolved(
            open,
            consequence,
            returned,
            consequence_cut,
            return_cut,
            plan,
        )
    }

    pub fn close_resolved(
        &mut self,
        open: OpenContact,
        consequence: Arc<ActiveCut>,
        returned: PreparedContact,
        consequence_cut: u64,
        return_cut: u64,
        plan: SettlementPlan,
    ) -> Result<ClosedContact, ContactCycleError> {
        self.commit_consequence(&open, consequence, consequence_cut)?;
        let pending = self.commit_returned(open, returned, return_cut, plan)?;
        self.finish_returned(pending)
    }

    /// Record the already-enacted world consequence before any returned current is conducted.
    /// Repeating the exact consequence for this transition is idempotent.
    pub fn commit_consequence(
        &mut self,
        open: &OpenContact,
        consequence: Arc<ActiveCut>,
        consequence_cut: u64,
    ) -> Result<(), ContactCycleError> {
        if !Arc::ptr_eq(&open.owner, &self.owner) {
            return Err(ContactCycleError::ReceiverChanged);
        }
        if !self.holon.open_enacted_is(open.transition, &open.deed)? {
            return Err(ContactCycleError::ReceiverChanged);
        }
        self.holon
            .commit_consequence(open.transition, consequence, consequence_cut)?;
        Ok(())
    }

    /// Commit an already-conducted returned population and its complete settlement at phase five.
    /// The new receiver stands immediately; closing the after role is a separate replay-free step.
    pub fn commit_returned(
        &mut self,
        open: OpenContact,
        mut returned: PreparedContact,
        return_cut: u64,
        plan: SettlementPlan,
    ) -> Result<PendingAfterContact, ContactCycleError> {
        if !Arc::ptr_eq(&open.owner, &self.owner) {
            return Err(ContactCycleError::ReceiverChanged);
        }
        if returned.generation != self.generation {
            return Err(ContactCycleError::ReceiverChanged);
        }
        let next_generation = self
            .generation
            .checked_add(1)
            .ok_or(ContactCycleError::ResourceExtent)?;
        returned.enacted.prepare_cut(return_cut, &self.standing)?;
        let prepared_cut = returned
            .enacted
            .prepared_cut(return_cut)
            .ok_or(ContactCycleError::CutAbsent(return_cut))?;
        let successor = prepared_cut.successor.clone();
        let (ended, ancestry) = self.validate_return_settlement(&open, &returned.enacted, &plan)?;
        let (source_rows, origin_rows, lineage_rows) = plan.abi_populations()?;
        let enactment = self.next_enactment;
        let next_enactment = enactment
            .checked_add(1)
            .ok_or(ContactCycleError::ResourceExtent)?;
        returned
            .enacted
            .install_lineages(self.owner.id, enactment, Some(&ancestry))?;
        let enacted = Arc::new(returned.enacted);
        self.enacted
            .try_reserve(1)
            .map_err(|_| ContactCycleError::ResourceReservation)?;
        self.preflight_claims(enacted.mounts())?;
        self.validate_ended(&ended, enacted.mounts())?;
        self.preflight_new_lineages(&enacted)?;
        if !self.holon.open_enacted_is(open.transition, &open.deed)? {
            return Err(ContactCycleError::ReceiverChanged);
        }
        self.holon.commit_returned(
            open.transition,
            enacted.clone(),
            return_cut,
            &source_rows,
            &origin_rows,
            &lineage_rows,
        )?;

        self.enacted.push(enacted.clone());
        self.install_claims(enacted.mounts());
        self.install_ended(&ended);
        self.install_new_lineages(&enacted);
        self.standing = successor;
        self.generation = next_generation;
        self.next_enactment = next_enactment;
        Ok(PendingAfterContact {
            transition: open.transition,
            owner: self.owner.clone(),
            source: open.deed,
            source_cut: open.deed_cut,
            returned: enacted,
            return_cut,
            after: self.standing.clone(),
        })
    }

    /// Recover the exact phase-five capability from the live Holon.
    pub fn pending_after(
        &self,
        transition: TransitionId,
    ) -> Result<PendingAfterContact, ContactCycleError> {
        let (source, source_cut, returned, return_cut) =
            self.holon.phase_five_surfaces(transition)?;
        if !self
            .enacted
            .iter()
            .any(|candidate| Arc::ptr_eq(candidate, &source))
            || !self
                .enacted
                .iter()
                .any(|candidate| Arc::ptr_eq(candidate, &returned))
        {
            return Err(ContactCycleError::RecoveryIdentity);
        }
        let after = returned
            .prepared_cut(return_cut)
            .and_then(|prepared| {
                (prepared.successor.as_ref() == self.standing.as_ref())
                    .then(|| prepared.successor.clone())
            })
            .ok_or(ContactCycleError::RecoveryTopology)?;
        Ok(PendingAfterContact {
            transition,
            owner: self.owner.clone(),
            source,
            source_cut,
            returned,
            return_cut,
            after,
        })
    }

    /// Close only the phase-five after role. No source, world, or returned action is repeated.
    pub fn finish_returned(
        &mut self,
        pending: PendingAfterContact,
    ) -> Result<ClosedContact, ContactCycleError> {
        if !Arc::ptr_eq(&pending.owner, &self.owner) || !Arc::ptr_eq(&pending.after, &self.standing)
        {
            return Err(ContactCycleError::ReceiverChanged);
        }
        let (source, source_cut, returned, return_cut) =
            self.holon.phase_five_surfaces(pending.transition)?;
        if !Arc::ptr_eq(&source, &pending.source)
            || !Arc::ptr_eq(&returned, &pending.returned)
            || source_cut != pending.source_cut
            || return_cut != pending.return_cut
        {
            return Err(ContactCycleError::ReceiverChanged);
        }
        let receipt = self
            .holon
            .finish_returned(pending.transition, pending.after)?;
        Ok(ClosedContact {
            transition: pending.transition,
            receipt,
            owner: self.owner.clone(),
            source: pending.source,
            source_cut: pending.source_cut,
            returned: pending.returned,
            return_cut: pending.return_cut,
        })
    }

    /// Settle an exact no-world-action contact. The source commit has already advanced the body;
    /// this operation appends only its actual after face and advances neither generation nor
    /// enactment.
    pub fn settle_silent(&mut self, open: OpenContact) -> Result<SilentContact, ContactCycleError> {
        if !Arc::ptr_eq(&open.owner, &self.owner) {
            return Err(ContactCycleError::ReceiverChanged);
        }
        if !self.holon.open_enacted_is(open.transition, &open.deed)? {
            return Err(ContactCycleError::ReceiverChanged);
        }
        for current in 0..open.deed.active.header.currents() {
            let state = open
                .current_contact_state(current)
                .ok_or(ContactCycleError::ResourceExtent)?;
            if state.unresolved() {
                return Err(ContactCycleError::SettlementUnresolved(current));
            }
            if state.contacted() {
                return Err(ContactCycleError::SettlementContact(current));
            }
            let lineage = open
                .lineage(current)
                .ok_or(ContactCycleError::LineageAbsent(current))?;
            self.validate_live_lineage(current, &lineage)?;
        }
        let source_extent = usize::try_from(open.deed.active.header.currents())
            .map_err(|_| ContactCycleError::ResourceExtent)?;
        let mut sources = Vec::new();
        sources
            .try_reserve_exact(source_extent)
            .map_err(|_| ContactCycleError::ResourceReservation)?;
        sources.resize(source_extent, SourceDisposition::Standing.abi());
        let receipt = self
            .holon
            .settle_silent(open.transition, self.standing.clone(), &sources)?;
        Ok(SilentContact {
            transition: open.transition,
            receipt,
            owner: self.owner.clone(),
            source: open.deed,
            source_cut: open.deed_cut,
        })
    }
}

#[cfg(test)]
fn prepare_with_order(
    active: Arc<ActiveCut>,
    standing: &SparseStandingSurface,
    generation: u64,
    order: impl IntoIterator<Item = u64>,
) -> Result<PreparedContact, ContactCycleError> {
    let mounts = birth_mounts(active.header.currents())?;
    let mut prepared = prepare_host_with_order(active, standing, generation, mounts, order)?;
    prepared.enacted.prepare_cut(0, standing)?;
    Ok(prepared)
}

#[cfg(test)]
fn prepare_with_mounts_and_order(
    active: Arc<ActiveCut>,
    standing: &SparseStandingSurface,
    generation: u64,
    _owner: &Arc<EcologyOwner>,
    mounts: Vec<CurrentMount>,
    order: impl IntoIterator<Item = u64>,
) -> Result<PreparedContact, ContactCycleError> {
    prepare_host_with_order(active, standing, generation, mounts, order)
}

fn birth_mounts(currents: u64) -> Result<Vec<CurrentMount>, ContactCycleError> {
    let extent = usize::try_from(currents).map_err(|_| ContactCycleError::ResourceExtent)?;
    let mut mounts = Vec::new();
    mounts
        .try_reserve_exact(extent)
        .map_err(|_| ContactCycleError::ResourceReservation)?;
    mounts.resize_with(extent, || CurrentMount::Birth);
    Ok(mounts)
}

fn prepare_host_with_order(
    active: Arc<ActiveCut>,
    standing: &SparseStandingSurface,
    generation: u64,
    mounts: Vec<CurrentMount>,
    order: impl IntoIterator<Item = u64>,
) -> Result<PreparedContact, ContactCycleError> {
    if mounts.len()
        != usize::try_from(active.header.currents())
            .map_err(|_| ContactCycleError::ResourceExtent)?
    {
        return Err(ContactCycleError::CurrentMountExtent);
    }
    let validated = active.validated()?;
    let event_topology = EventTopology::new_validated(validated)?;
    let (mut directed_contacts, incoming_directed) =
        prepare_directed_contacts(&active, &event_topology)?;
    let current_extent =
        usize::try_from(active.header.currents()).map_err(|_| ContactCycleError::ResourceExtent)?;
    let mut outcomes = Vec::new();
    outcomes
        .try_reserve_exact(current_extent)
        .map_err(|_| ContactCycleError::ResourceReservation)?;
    for _ in 0..current_extent {
        outcomes.push(None);
    }
    let mut parts = Vec::new();
    parts
        .try_reserve_exact(current_extent)
        .map_err(|_| ContactCycleError::ResourceReservation)?;

    for ordinal in order {
        let slot = outcomes
            .get_mut(
                usize::try_from(ordinal)
                    .map_err(|_| ContactCycleError::CurrentSchedule(ordinal))?,
            )
            .ok_or(ContactCycleError::CurrentSchedule(ordinal))?;
        if slot.is_some() {
            return Err(ContactCycleError::CurrentSchedule(ordinal));
        }
        let (preflight, mut builder) =
            preflight_current_partition_validated(validated, ordinal, 1)?;
        let contacts_extent = usize::try_from(preflight.bright_events)
            .map_err(|_| ContactCycleError::ResourceExtent)?;
        let mut event_contacts = Vec::new();
        event_contacts
            .try_reserve_exact(contacts_extent)
            .map_err(|_| ContactCycleError::ResourceReservation)?;
        let prior = match mounts.get(ordinal as usize) {
            Some(CurrentMount::Birth) => None,
            Some(CurrentMount::Continue(lineage)) => Some(lineage.carrier()),
            None => return Err(ContactCycleError::CurrentMountExtent),
        };
        // §XXXII-c: every later current owns a fresh local REGISTER. The predecessor's OWN
        // population remains exact testimony and has already entered the receiver standing face;
        // carrying it here would count the same construction twice.
        let mut own = GrowingRankedOwn::new();
        let mut carrier = match prior {
            Some(prior) => prior.carrier().branch_shared(),
            None => {
                GrowingCarrier::with_depth(1).map_err(|_| ContactCycleError::ResourceReservation)?
            }
        };
        let current = active.currents[ordinal as usize];
        let first_event = event_topology
            .event(current.event_offset())
            .ok_or(ContactCycleError::CurrentBirth(ordinal))?;

        let state;
        {
            let mut body = match prior {
                Some(prior) => ErosBody::resume_standing_world_ranked_storage_from_live_header(
                    standing,
                    &mut own,
                    prior.header(),
                    &mut carrier,
                ),
                None => ErosBody::over_standing_world_ranked_storage_from_first_difference(
                    standing,
                    &mut own,
                    first_event.node().place,
                    &mut carrier,
                ),
            }
            .ok_or(ContactCycleError::CurrentBirth(ordinal))?;
            let mut before_event =
                |event: u64, body: &mut ErosBody<'_>| -> Result<(), ConductError> {
                    let first = incoming_directed.partition_point(|row| row.event < event);
                    let after = incoming_directed.partition_point(|row| row.event <= event);
                    if first == after {
                        return Ok(());
                    }
                    // All incident hands at this target read one exact pre-event receiver. None may
                    // observe a sibling's candidate relation or mutate the target current on its way
                    // into the later order-free cut fold.
                    let receiver = body.event_receiver();
                    for row in &incoming_directed[first..after] {
                        let contact = directed_contacts
                            .get_mut(row.contact)
                            .ok_or(ConductError::ResourceExtent)?;
                        contact.resolve(body.directed_event_contact(
                            receiver,
                            contact.from_place().ok_or(ConductError::ResourceExtent)?,
                            contact.to_place().ok_or(ConductError::ResourceExtent)?,
                        ));
                    }
                    Ok(())
                };
            let conduct = conduct_current_partition_with_event_receiver(
                validated,
                ordinal,
                &mut body,
                &mut builder,
                &mut before_event,
                |contact| event_contacts.push(contact),
            )?;
            if body.resource_refused() || event_contacts.len() != contacts_extent {
                return Err(ContactCycleError::ResourceReservation);
            }
            let cursor = current
                .event_offset()
                .checked_add(current.events())
                .ok_or(ContactCycleError::ResourceExtent)?;
            let live_header = body.live_header(cursor);
            state = (
                conduct,
                body.own_rank(),
                body.breath(),
                body.deposited_terms(),
                live_header,
                body.thoughts(),
            );
        }
        let mut own_occupancy = Vec::new();
        own_occupancy
            .try_reserve_exact(own.occupancy_words().len())
            .map_err(|_| ContactCycleError::ResourceReservation)?;
        own_occupancy.extend_from_slice(own.occupancy_words());
        let mut own_cells = Vec::new();
        own_cells
            .try_reserve_exact(own.cells().len())
            .map_err(|_| ContactCycleError::ResourceReservation)?;
        own_cells.extend_from_slice(own.cells());
        let carrier = Arc::new(
            LiveCarrierSnapshot::new(state.4, carrier)
                .map_err(|_| ContactCycleError::ResourceReservation)?,
        );
        let outcome = CurrentOutcome {
            conduct: state.0,
            contacts: event_contacts,
            own_rank: state.1,
            own_occupancy,
            breath: state.2,
            own_cells,
            terms: state.3,
            carrier,
            thoughts: state.5,
        };
        *slot = Some(outcome);
        parts.push(builder.finish()?);
    }

    let mut ordered = Vec::new();
    ordered
        .try_reserve_exact(current_extent)
        .map_err(|_| ContactCycleError::ResourceReservation)?;
    for (ordinal, outcome) in outcomes.into_iter().enumerate() {
        ordered.push(outcome.ok_or(ContactCycleError::CurrentSchedule(ordinal as u64))?);
    }
    if let Some(contact) = directed_contacts
        .iter()
        .copied()
        .find(|contact| contact.needs_resolution())
    {
        return Err(ContactCycleError::DirectedUnresolved(contact.directed()));
    }

    let emissions = EmissionJournal::assemble_validated(validated, parts)?;
    let event_surfaces = event_topology.into_events();
    let topology = ActiveTopology::new_validated(validated, &emissions, directed_contacts)?;
    let (carried, incidence_surface, directed_contacts) = topology.into_owned_parts();
    Ok(PreparedContact {
        generation,
        enacted: EnactedPopulation {
            active,
            event_surfaces,
            emissions,
            currents: ordered,
            carried,
            incidence_surface,
            directed_contacts,
            prepared_cut: None,
            mounts,
            lineages: Vec::new(),
        },
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use body::medium::{RegionalForm, FORM_WORDS};
    use body::num::Cog;
    use soma_abi::active::{
        ActionCurrent, CurrentSpan, CutSpan, DirectedIncidence, EventSpan, Incidence, OriginRef,
        RelationAtom,
    };
    use soma_abi::emission::DeedKind;

    fn heterogeneous_cut() -> Arc<ActiveCut> {
        let relations = [
            Cog::lit(3),
            Cog::lit(-5),
            Cog::lit(8),
            Cog::lit(13),
            Cog::lit(-21),
            Cog::lit(34),
            Cog::lit(257).turn_up(1),
            Cog::lit(-65_537).turn_down(2).turned(1),
            Cog::lit(144),
            Cog::lit(233),
            Cog::lit(-377),
            Cog::lit(610),
        ];
        Arc::new(
            ActiveCut::new(
                relations
                    .iter()
                    .copied()
                    .map(|relation| RelationAtom::new(relation).unwrap())
                    .collect(),
                (0..relations.len())
                    .map(|event| EventSpan::new(event as u64, 1).unwrap())
                    .collect(),
                vec![ActionCurrent::new(Cog::lit(1)).unwrap(); relations.len()],
                (0..relations.len())
                    .map(|event| OriginRef::new(if event < 6 { 11 } else { 29 }, event as u64))
                    .collect(),
                vec![
                    CurrentSpan::new(0, 6, 0, 6).unwrap(),
                    CurrentSpan::new(6, 6, 6, 6).unwrap(),
                ],
                vec![CutSpan::new(0, 2, 0, 1).unwrap()],
                vec![
                    Incidence::new(0, 0, 6).unwrap(),
                    Incidence::new(1, 0, 6).unwrap(),
                ],
                vec![DirectedIncidence::new(0, 1)],
            )
            .unwrap(),
        )
    }

    fn reorigined(active: &ActiveCut, organ: u64, occurrence: u64) -> Arc<ActiveCut> {
        Arc::new(
            ActiveCut::new(
                active.atoms.clone(),
                active.events.clone(),
                active.actions.clone(),
                (0..active.events.len())
                    .map(|event| OriginRef::new(organ, occurrence + event as u64))
                    .collect(),
                active.currents.clone(),
                active.cuts.clone(),
                active.incidences.clone(),
                active.directed.clone(),
            )
            .unwrap(),
        )
    }

    fn plural_directed_interior_cut(interior: i64) -> Arc<ActiveCut> {
        let values = [1, 2, interior, 4, 5, 6, 7, 8];
        Arc::new(
            ActiveCut::new(
                values
                    .iter()
                    .map(|value| RelationAtom::new(Cog::lit(*value)).unwrap())
                    .collect(),
                (0..values.len())
                    .map(|event| EventSpan::new(event as u64, 1).unwrap())
                    .collect(),
                vec![ActionCurrent::new(Cog::lit(1)).unwrap(); values.len()],
                (0..values.len())
                    .map(|event| OriginRef::new(97, event as u64))
                    .collect(),
                vec![CurrentSpan::new(0, values.len() as u64, 0, values.len() as u64).unwrap()],
                vec![CutSpan::new(0, 3, 0, 1).unwrap()],
                vec![
                    Incidence::new(0, 0, 6).unwrap(),
                    Incidence::new(0, 6, 1).unwrap(),
                    Incidence::new(0, 7, 1).unwrap(),
                ],
                vec![DirectedIncidence::new(0, 2)],
            )
            .unwrap(),
        )
    }

    fn relation_cut(values: &[i64], organ: u64, occurrence: u64) -> Arc<ActiveCut> {
        Arc::new(
            ActiveCut::new(
                values
                    .iter()
                    .map(|value| RelationAtom::new(Cog::lit(*value)).unwrap())
                    .collect(),
                (0..values.len())
                    .map(|at| EventSpan::new(at as u64, 1).unwrap())
                    .collect(),
                vec![ActionCurrent::new(Cog::lit(1)).unwrap(); values.len()],
                (0..values.len())
                    .map(|at| OriginRef::new(organ, occurrence + at as u64))
                    .collect(),
                vec![CurrentSpan::new(0, values.len() as u64, 0, values.len() as u64).unwrap()],
                vec![CutSpan::new(0, 1, 0, 0).unwrap()],
                vec![Incidence::new(0, 0, values.len() as u64).unwrap()],
                Vec::new(),
            )
            .unwrap(),
        )
    }

    fn single_relation_cut(value: i64, organ: u64, occurrence: u64) -> Arc<ActiveCut> {
        relation_cut(&[value], organ, occurrence)
    }

    fn two_receiving_cuts() -> Arc<ActiveCut> {
        Arc::new(
            ActiveCut::new(
                vec![RelationAtom::new(Cog::lit(13)).unwrap()],
                vec![EventSpan::new(0, 1).unwrap()],
                vec![ActionCurrent::new(Cog::lit(1)).unwrap()],
                vec![OriginRef::new(41, 0)],
                vec![CurrentSpan::new(0, 1, 0, 1).unwrap()],
                vec![
                    CutSpan::new(0, 1, 0, 0).unwrap(),
                    CutSpan::new(1, 1, 0, 0).unwrap(),
                ],
                vec![
                    Incidence::new(0, 0, 1).unwrap(),
                    Incidence::new(0, 0, 1).unwrap(),
                ],
                vec![],
            )
            .unwrap(),
        )
    }

    fn exact_directed_cut(directed_hand: Option<bool>) -> Arc<ActiveCut> {
        let values = [1, 2, 3, 4, 5, 6, 7, 8];
        let cuts = if directed_hand.is_some() {
            vec![CutSpan::new(0, 3, 0, 1).unwrap()]
        } else {
            vec![CutSpan::new(0, 3, 0, 0).unwrap()]
        };
        let directed = directed_hand.map_or_else(Vec::new, |reverse| {
            vec![if reverse {
                DirectedIncidence::new(2, 1)
            } else {
                DirectedIncidence::new(1, 2)
            }]
        });
        Arc::new(
            ActiveCut::new(
                values
                    .iter()
                    .map(|value| RelationAtom::new(Cog::lit(*value)).unwrap())
                    .collect(),
                (0..values.len())
                    .map(|event| EventSpan::new(event as u64, 1).unwrap())
                    .collect(),
                vec![ActionCurrent::new(Cog::lit(1)).unwrap(); values.len()],
                (0..values.len())
                    .map(|event| OriginRef::new(83, event as u64))
                    .collect(),
                vec![CurrentSpan::new(0, values.len() as u64, 0, values.len() as u64).unwrap()],
                cuts,
                vec![
                    Incidence::new(0, 0, (values.len() - 2) as u64).unwrap(),
                    Incidence::new(0, (values.len() - 2) as u64, 1).unwrap(),
                    Incidence::new(0, (values.len() - 1) as u64, 1).unwrap(),
                ],
                directed,
            )
            .unwrap(),
        )
    }

    fn one_event_current_population(relations: &[Cog], organ: u64) -> Arc<ActiveCut> {
        let extent = u64::try_from(relations.len()).unwrap();
        Arc::new(
            ActiveCut::new(
                relations
                    .iter()
                    .copied()
                    .map(|relation| RelationAtom::new(relation).unwrap())
                    .collect(),
                (0..extent)
                    .map(|event| EventSpan::new(event, 1).unwrap())
                    .collect(),
                (0..extent)
                    .map(|event| {
                        ActionCurrent::new(Cog::lit(event as i64 + 1).turned(event as u32)).unwrap()
                    })
                    .collect(),
                (0..extent)
                    .map(|event| OriginRef::new(organ, event))
                    .collect(),
                (0..extent)
                    .map(|current| CurrentSpan::new(current, 1, current, 1).unwrap())
                    .collect(),
                vec![CutSpan::new(0, extent, 0, 0).unwrap()],
                (0..extent)
                    .map(|current| Incidence::new(current, 0, 1).unwrap())
                    .collect(),
                Vec::new(),
            )
            .unwrap(),
        )
    }

    fn canceling_dark_population(actions: &[Cog], organ: u64) -> Arc<ActiveCut> {
        let currents = u64::try_from(actions.len()).unwrap();
        let events = currents.checked_mul(2).unwrap();
        let mut action_rows = Vec::with_capacity(actions.len() * 2);
        for action in actions {
            action_rows.push(ActionCurrent::new(*action).unwrap());
            action_rows.push(ActionCurrent::new(action.turned(2)).unwrap());
        }
        Arc::new(
            ActiveCut::new(
                vec![RelationAtom::new(Cog::ZERO).unwrap(); events as usize],
                (0..events)
                    .map(|event| EventSpan::new(event, 1).unwrap())
                    .collect(),
                action_rows,
                (0..events)
                    .map(|event| OriginRef::new(organ, event))
                    .collect(),
                (0..currents)
                    .map(|current| {
                        let offset = current * 2;
                        CurrentSpan::new(offset, 2, offset, 2).unwrap()
                    })
                    .collect(),
                vec![CutSpan::new(0, currents, 0, 0).unwrap()],
                (0..currents)
                    .map(|current| Incidence::new(current, 0, 2).unwrap())
                    .collect(),
                Vec::new(),
            )
            .unwrap(),
        )
    }

    /// Four source currents: one lawful silent occurrence followed by three independently
    /// contacted eight-event relations.  Every row is numerical/topological material; no text,
    /// file, semantic tag, or receiver category participates.
    fn mixed_fate_source_cut() -> Arc<ActiveCut> {
        let mut relations = vec![Cog::ZERO, Cog::ZERO];
        for _ in 0..3 {
            relations.extend((1..=8).map(Cog::lit));
        }
        let events = u64::try_from(relations.len()).unwrap();
        let dark_action = Cog::lit(257).turn_up(3).turned(1);
        let mut actions = vec![
            ActionCurrent::new(dark_action).unwrap(),
            ActionCurrent::new(dark_action.turned(2)).unwrap(),
        ];
        actions.extend(vec![ActionCurrent::new(Cog::lit(1)).unwrap(); 24]);
        Arc::new(
            ActiveCut::new(
                relations
                    .iter()
                    .copied()
                    .map(|relation| RelationAtom::new(relation).unwrap())
                    .collect(),
                (0..events)
                    .map(|event| EventSpan::new(event, 1).unwrap())
                    .collect(),
                actions,
                (0..events)
                    .map(|event| OriginRef::new(0x4d49_5845_44, event))
                    .collect(),
                vec![
                    CurrentSpan::new(0, 2, 0, 2).unwrap(),
                    CurrentSpan::new(2, 8, 2, 8).unwrap(),
                    CurrentSpan::new(10, 8, 10, 8).unwrap(),
                    CurrentSpan::new(18, 8, 18, 8).unwrap(),
                ],
                vec![CutSpan::new(0, events, 0, 3).unwrap()],
                vec![
                    Incidence::new(0, 0, 1).unwrap(),
                    Incidence::new(0, 1, 1).unwrap(),
                    Incidence::new(1, 0, 1).unwrap(),
                    Incidence::new(1, 1, 1).unwrap(),
                    Incidence::new(1, 2, 1).unwrap(),
                    Incidence::new(1, 3, 1).unwrap(),
                    Incidence::new(1, 4, 1).unwrap(),
                    Incidence::new(1, 5, 1).unwrap(),
                    Incidence::new(1, 6, 1).unwrap(),
                    Incidence::new(1, 7, 1).unwrap(),
                    Incidence::new(2, 0, 1).unwrap(),
                    Incidence::new(2, 1, 1).unwrap(),
                    Incidence::new(2, 2, 1).unwrap(),
                    Incidence::new(2, 3, 1).unwrap(),
                    Incidence::new(2, 4, 1).unwrap(),
                    Incidence::new(2, 5, 1).unwrap(),
                    Incidence::new(2, 6, 1).unwrap(),
                    Incidence::new(2, 7, 1).unwrap(),
                    Incidence::new(3, 0, 1).unwrap(),
                    Incidence::new(3, 1, 1).unwrap(),
                    Incidence::new(3, 2, 1).unwrap(),
                    Incidence::new(3, 3, 1).unwrap(),
                    Incidence::new(3, 4, 1).unwrap(),
                    Incidence::new(3, 5, 1).unwrap(),
                    Incidence::new(3, 6, 1).unwrap(),
                    Incidence::new(3, 7, 1).unwrap(),
                ],
                vec![
                    DirectedIncidence::new(8, 9),
                    DirectedIncidence::new(16, 17),
                    DirectedIncidence::new(24, 25),
                ],
            )
            .unwrap(),
        )
    }

    fn first_contacted_incidence(open: &OpenContact, current: u64) -> (u64, u64) {
        let carried = open.carried_cut();
        for incidence in 0..carried.incidence_count() {
            let row = open.deed.active.incidences[incidence as usize];
            if row.current() != current {
                continue;
            }
            for event in 0..row.current_events() {
                if carried.incidence_event_contacted(incidence, event).unwrap() {
                    return (incidence, event);
                }
            }
        }
        panic!("current {current} has no actual contacted occurrence")
    }

    type CurrentFace = (
        u64,
        Vec<u64>,
        Vec<RankedOwnCell>,
        LiveBodyHeader,
        Vec<u32>,
        Vec<Vec<body::manifold::Node>>,
    );

    fn face(contact: &PreparedContact) -> Vec<CurrentFace> {
        contact
            .enacted
            .currents
            .iter()
            .map(|current| {
                let carrier = current.carrier.carrier();
                let carrier_words = carrier.words().to_vec();
                let mut overflow: Vec<_> = Default::default();
                for depth in 0..carrier.depth() {
                    overflow.push(carrier.co_present_overflow(depth).unwrap().to_vec());
                }
                (
                    current.own_rank,
                    current.own_occupancy.clone(),
                    current.own_cells.clone(),
                    current.carrier.header(),
                    carrier_words,
                    overflow,
                )
            })
            .collect()
    }

    #[test]
    fn whole_contact_is_schedule_gauge_and_retains_plural_organs_and_hand() {
        let active = heterogeneous_cut();
        let standing = SparseStandingSurface::empty(64).unwrap();
        let forward = prepare_with_order(active.clone(), &standing, 0, [0, 1]).unwrap();
        let reverse = prepare_with_order(active.clone(), &standing, 0, [1, 0]).unwrap();
        assert_eq!(forward.enacted.emissions, reverse.enacted.emissions);
        assert_eq!(face(&forward), face(&reverse));
        assert_eq!(
            forward.enacted.prepared_cut(0).unwrap().fold,
            reverse.enacted.prepared_cut(0).unwrap().fold
        );
        assert_eq!(
            forward.enacted.prepared_cut(0).unwrap().successor,
            reverse.enacted.prepared_cut(0).unwrap().successor
        );
        assert_eq!(active.origins[0].organ(), 11);
        assert_eq!(active.origins[6].organ(), 29);
        assert_eq!(active.directed, vec![DirectedIncidence::new(0, 1)]);
        assert!(!matches!(
            forward.enacted.directed_contacts()[0].resolution(),
            crate::DirectedResolution::SpanEndpointOpen
        ));
        assert_eq!(
            forward.enacted.directed_contacts()[0].resolution(),
            reverse.enacted.directed_contacts()[0].resolution(),
            "the complete plural-section endpoint is schedule gauge"
        );
        assert_eq!(forward.enacted.currents[0].contacts.len(), 6);
        assert_eq!(forward.enacted.currents[1].contacts.len(), 6);

        let prepared = forward.enacted.prepared_cut(0).unwrap();
        let fold = &prepared.fold;
        let successor = prepared.successor.as_ref();
        let axis = successor.flat_axis().unwrap() as usize;
        let mut dense = vec![0u32; axis * axis * FORM_WORDS];
        fold.commit(&mut dense).unwrap();
        let mut occupied = 0usize;
        for grip in 0..axis * axis {
            let form = RegionalForm::unpack(&dense, grip * FORM_WORDS);
            if form.occupied() {
                occupied += 1;
            }
            assert_eq!(form, successor.form_at(grip as u32));
        }
        assert_eq!(occupied, successor.cells().len());
    }

    #[test]
    fn opaque_origin_changes_neither_typed_conduct_nor_cut_topology() {
        let source = heterogeneous_cut();
        let sibling = reorigined(&source, 0xfeed, 10_000);
        assert_ne!(source.origins, sibling.origins);
        assert_eq!(source.atoms, sibling.atoms);
        assert_eq!(source.events, sibling.events);
        assert_eq!(source.actions, sibling.actions);
        assert_eq!(source.currents, sibling.currents);
        assert_eq!(source.cuts, sibling.cuts);
        assert_eq!(source.incidences, sibling.incidences);
        assert_eq!(source.directed, sibling.directed);

        let standing = SparseStandingSurface::empty_rank(80).unwrap();
        let left = prepare_with_order(source, &standing, 0, [0, 1]).unwrap();
        let right = prepare_with_order(sibling, &standing, 0, [1, 0]).unwrap();
        assert_eq!(left.enacted.emissions(), right.enacted.emissions());
        assert_eq!(face(&left), face(&right));
        assert_eq!(
            left.enacted.prepared_cut(0).unwrap().fold(),
            right.enacted.prepared_cut(0).unwrap().fold()
        );
        assert_eq!(
            left.enacted.prepared_cut(0).unwrap().successor(),
            right.enacted.prepared_cut(0).unwrap().successor()
        );
    }

    #[test]
    fn every_interior_event_of_a_plural_directed_section_changes_its_contact() {
        let standing = SparseStandingSurface::empty_rank(80).unwrap();
        let left = prepare_with_order(plural_directed_interior_cut(3), &standing, 0, [0]).unwrap();
        let right =
            prepare_with_order(plural_directed_interior_cut(257), &standing, 0, [0]).unwrap();
        assert_eq!(
            left.enacted.event_surface(0),
            right.enacted.event_surface(0)
        );
        assert_eq!(
            left.enacted.event_surface(5),
            right.enacted.event_surface(5)
        );
        assert_ne!(
            left.enacted.event_surface(2),
            right.enacted.event_surface(2)
        );
        assert!(matches!(
            left.enacted.directed_contacts()[0].resolution(),
            crate::DirectedResolution::Crossed(_)
        ));
        assert!(matches!(
            right.enacted.directed_contacts()[0].resolution(),
            crate::DirectedResolution::Crossed(_)
        ));
        assert_ne!(
            left.enacted.directed_contacts()[0].resolution(),
            right.enacted.directed_contacts()[0].resolution(),
            "the complete ordered source section, including its interior, is the endpoint"
        );
        assert_ne!(
            left.enacted.prepared_cut(0).unwrap().fold(),
            right.enacted.prepared_cut(0).unwrap().fold()
        );
        assert_ne!(
            left.enacted.prepared_cut(0).unwrap().successor(),
            right.enacted.prepared_cut(0).unwrap().successor()
        );
    }

    #[test]
    fn exact_event_hand_crosses_at_the_target_receiver_and_reversal_changes_the_fold() {
        let standing = SparseStandingSurface::empty(64).unwrap();
        let control = prepare_with_order(exact_directed_cut(None), &standing, 0, [0]).unwrap();
        let forward =
            prepare_with_order(exact_directed_cut(Some(false)), &standing, 0, [0]).unwrap();
        let reverse =
            prepare_with_order(exact_directed_cut(Some(true)), &standing, 0, [0]).unwrap();
        assert!(control.enacted.directed_contacts().is_empty());
        assert_eq!(forward.enacted.directed_contacts().len(), 1);
        assert_eq!(reverse.enacted.directed_contacts().len(), 1);
        assert!(matches!(
            forward.enacted.directed_contacts()[0].resolution(),
            crate::DirectedResolution::Crossed(_)
        ));
        assert!(matches!(
            reverse.enacted.directed_contacts()[0].resolution(),
            crate::DirectedResolution::Crossed(_)
        ));
        assert_ne!(
            forward.enacted.directed_contacts()[0].resolution(),
            reverse.enacted.directed_contacts()[0].resolution()
        );
        assert_ne!(
            forward.enacted.prepared_cut(0).unwrap().fold(),
            reverse.enacted.prepared_cut(0).unwrap().fold()
        );
        assert_ne!(
            control.enacted.prepared_cut(0).unwrap().fold(),
            forward.enacted.prepared_cut(0).unwrap().fold(),
            "an actual supplied A2 edge contributes where the same undirected population cannot"
        );
        assert_ne!(
            forward.enacted.prepared_cut(0).unwrap().successor(),
            reverse.enacted.prepared_cut(0).unwrap().successor()
        );
    }

    #[test]
    fn mounted_current_schedule_is_gauge_while_the_parent_map_stays_exact() {
        let mut ecology = LiveEcology::new(
            EcologyId::new(1, 1),
            SparseStandingSurface::empty(64).unwrap(),
        );
        let initial = ecology.prepare(heterogeneous_cut()).unwrap();
        let open = ecology.commit(initial, 0).unwrap();
        let mounts = vec![
            CurrentMount::Continue(open.lineage(0).unwrap()),
            CurrentMount::Continue(open.lineage(1).unwrap()),
        ];
        let active = heterogeneous_cut();
        let mut forward = prepare_with_mounts_and_order(
            active.clone(),
            &ecology.standing,
            ecology.generation,
            &ecology.owner,
            mounts.clone(),
            [0, 1],
        )
        .unwrap();
        let mut reverse = prepare_with_mounts_and_order(
            active,
            &ecology.standing,
            ecology.generation,
            &ecology.owner,
            mounts,
            [1, 0],
        )
        .unwrap();
        forward.enacted.prepare_cut(0, &ecology.standing).unwrap();
        reverse.enacted.prepare_cut(0, &ecology.standing).unwrap();
        assert_eq!(forward.enacted.emissions, reverse.enacted.emissions);
        assert_eq!(face(&forward), face(&reverse));
        assert_eq!(
            forward.enacted.prepared_cut(0).unwrap().fold,
            reverse.enacted.prepared_cut(0).unwrap().fold
        );
        assert_eq!(
            forward.enacted.prepared_cut(0).unwrap().successor,
            reverse.enacted.prepared_cut(0).unwrap().successor
        );
    }

    #[test]
    fn lineage_ownership_duplicate_parent_and_committed_reuse_are_refused() {
        let mut first = LiveEcology::new(
            EcologyId::new(2, 1),
            SparseStandingSurface::empty(64).unwrap(),
        );
        let initial = first
            .prepare(relation_cut(&[13, 29, 17, 31], 1, 0))
            .unwrap();
        let open = first.commit(initial, 0).unwrap();
        let parent = open.lineage(0).unwrap();
        let handle = parent.durable_handle();
        assert_eq!(handle.ecology(), first.id());
        assert_eq!(handle.enactment(), 0);
        assert_eq!(handle.current(), 0);
        assert_eq!(
            first.lineage(handle).unwrap().durable_handle(),
            handle,
            "one stable row resolves to the exact live enactment/current"
        );

        let foreign = LiveEcology::new(
            EcologyId::new(2, 2),
            SparseStandingSurface::empty(64).unwrap(),
        );
        assert!(foreign.lineage(handle).is_none());
        assert!(matches!(
            foreign.prepare_mounted(
                single_relation_cut(17, 2, 0),
                &[CurrentMount::Continue(parent.clone())]
            ),
            Err(ContactCycleError::ForeignLineage(0))
        ));

        assert!(matches!(
            first.prepare_mounted(
                heterogeneous_cut(),
                &[
                    CurrentMount::Continue(parent.clone()),
                    CurrentMount::Continue(parent.clone()),
                ]
            ),
            Err(ContactCycleError::DuplicateLineage(1))
        ));

        let returned = first
            .prepare_mounted(
                single_relation_cut(17, 3, 0),
                &[CurrentMount::Continue(parent.clone())],
            )
            .unwrap();
        first
            .close(open, single_relation_cut(19, 4, 0), returned, 0, 0)
            .unwrap();
        assert!(matches!(
            first.prepare_mounted(
                single_relation_cut(23, 5, 0),
                &[CurrentMount::Continue(parent)]
            ),
            Err(ContactCycleError::LineageClaimed(0))
        ));
    }

    #[test]
    fn silent_non_text_population_closes_with_live_sources_and_enumerable_settlement() {
        let mut ecology = LiveEcology::new(
            EcologyId::new(2, 3),
            SparseStandingSurface::empty_rank(80).unwrap(),
        );
        let active = canceling_dark_population(
            &[
                Cog::lit(257).turn_up(1),
                Cog::lit(-65_537).turn_down(2).turned(1),
            ],
            0x4f50_4151_5545,
        );
        let open = ecology
            .commit(ecology.prepare(active.clone()).unwrap(), 0)
            .unwrap();
        assert!(Arc::ptr_eq(open.carried_cut().active(), &active));
        assert!(open.current_contact_state(0).unwrap().settled_silent());
        assert!(open.current_contact_state(1).unwrap().settled_silent());
        let handles = [
            open.lineage(0).unwrap().durable_handle(),
            open.lineage(1).unwrap().durable_handle(),
        ];
        let generation = ecology.generation();
        let enacted = ecology.enacted().len();
        let standing = ecology.standing.clone();

        let silent = ecology.settle_silent(open).unwrap();
        assert_eq!(ecology.generation(), generation);
        assert_eq!(ecology.enacted().len(), enacted);
        assert!(Arc::ptr_eq(&ecology.standing, &standing));
        assert!(ecology.lineage(handles[0]).is_some());
        assert!(ecology.lineage(handles[1]).is_some());

        let header = ecology.holon().settlement_header().unwrap();
        assert_eq!(header.settlements(), 1);
        assert_eq!(header.silent_receipts(), 1);
        assert_eq!(header.source_dispositions(), 2);
        assert_eq!(header.return_origins(), 0);
        assert_eq!(header.lineage_incidences(), 0);
        let settlement = ecology.holon().settlement(silent.transition()).unwrap();
        assert_eq!(
            ecology.holon().settlement_at(0).unwrap().span(),
            settlement.span()
        );
        assert_eq!(settlement.span().kind(), soma_abi::holon::SETTLEMENT_SILENT);
        assert_eq!(
            settlement.sources(),
            &[
                SourceDispositionRow::standing(),
                SourceDispositionRow::standing(),
            ]
        );
        assert!(settlement.origins().is_empty());
        assert!(settlement.lineages().is_empty());
    }

    #[test]
    fn mixed_settlement_preserves_split_merge_end_and_event_multiplicity() {
        let mut ecology = LiveEcology::new(
            EcologyId::new(2, 4),
            SparseStandingSurface::empty_rank(80).unwrap(),
        );
        let source = mixed_fate_source_cut();
        let open = ecology.commit(ecology.prepare(source).unwrap(), 0).unwrap();
        assert!(open.current_contact_state(0).unwrap().settled_silent());
        for current in 1..4 {
            assert!(open.current_contact_state(current).unwrap().contacted());
        }
        let source_handles = [
            open.lineage(0).unwrap().durable_handle(),
            open.lineage(1).unwrap().durable_handle(),
            open.lineage(2).unwrap().durable_handle(),
            open.lineage(3).unwrap().durable_handle(),
        ];
        let source_1 = first_contacted_incidence(&open, 1);
        let source_2 = first_contacted_incidence(&open, 2);
        let source_3 = first_contacted_incidence(&open, 3);
        let returned_active = one_event_current_population(
            &[
                Cog::lit(313).turn_up(3),
                Cog::lit(-65_539).turn_down(1).turned(2),
                Cog::lit(997).turn_up(2).turned(3),
            ],
            0x5245_5455_524e,
        );
        let returned = ecology
            .prepare_mounted(
                returned_active,
                &[
                    CurrentMount::Continue(open.lineage(1).unwrap()),
                    CurrentMount::Birth,
                    CurrentMount::Birth,
                ],
            )
            .unwrap();
        let rows = vec![
            LineageIncidence::new(source_1.0, source_1.1, 0, 0),
            LineageIncidence::new(source_2.0, source_2.1, 1, 0),
            LineageIncidence::new(source_3.0, source_3.1, 1, 0),
            LineageIncidence::new(source_3.0, source_3.1, 2, 0),
            LineageIncidence::new(source_3.0, source_3.1, 2, 0),
        ];
        let closed = ecology
            .close_resolved(
                open,
                single_relation_cut(19, 0x434f_4e53_4551, 0),
                returned,
                0,
                0,
                SettlementPlan::new(
                    vec![
                        SourceDisposition::Standing,
                        SourceDisposition::Continued(0),
                        SourceDisposition::Ended,
                        SourceDisposition::Standing,
                    ],
                    vec![
                        ReturnOrigin::Continued(1),
                        ReturnOrigin::Birth,
                        ReturnOrigin::Birth,
                    ],
                    rows.clone(),
                ),
            )
            .unwrap();

        assert!(ecology.lineage(source_handles[0]).is_some());
        assert!(ecology.lineage(source_handles[1]).is_none());
        assert!(ecology.lineage(source_handles[2]).is_none());
        assert!(ecology.lineage(source_handles[3]).is_some());
        let returned = [
            closed.lineage(0).unwrap(),
            closed.lineage(1).unwrap(),
            closed.lineage(2).unwrap(),
        ];
        assert_eq!(returned[0].parents(), &[source_handles[1]]);
        assert_eq!(
            returned[1].parents(),
            &[source_handles[2], source_handles[3]]
        );
        assert_eq!(
            returned[2].parents(),
            &[source_handles[3], source_handles[3]],
            "equal parent handles retain distinct event-incidence multiplicity"
        );

        let header = ecology.holon().settlement_header().unwrap();
        assert_eq!(header.settlements(), 1);
        assert_eq!(header.silent_receipts(), 0);
        assert_eq!(header.source_dispositions(), 4);
        assert_eq!(header.return_origins(), 3);
        assert_eq!(header.lineage_incidences(), 5);
        let settlement = ecology.holon().settlement(closed.transition()).unwrap();
        assert_eq!(
            settlement.span().kind(),
            soma_abi::holon::SETTLEMENT_RETURNED
        );
        assert_eq!(
            ecology.holon().settlement_at(0).unwrap().span(),
            settlement.span()
        );
        assert_eq!(
            settlement.sources(),
            &[
                SourceDispositionRow::standing(),
                SourceDispositionRow::continued(0),
                SourceDispositionRow::ended(),
                SourceDispositionRow::standing(),
            ]
        );
        assert_eq!(
            settlement.origins(),
            &[
                ReturnOriginRow::continued(1),
                ReturnOriginRow::birth(),
                ReturnOriginRow::birth(),
            ]
        );
        assert_eq!(
            settlement.lineages(),
            rows.iter()
                .copied()
                .map(LineageIncidence::abi)
                .collect::<Vec<_>>()
        );

        let duplicate_parent_handle = returned[2].durable_handle();
        let image = ecology.rest_image().unwrap();
        let reopened = LiveEcology::from_rest_image(image).unwrap();
        assert_eq!(
            reopened.lineage(duplicate_parent_handle).unwrap().parents(),
            &[source_handles[3], source_handles[3]]
        );
    }

    #[test]
    fn a_rest_image_reopens_the_exact_live_carrier_without_replaying_a_deed() {
        let id = EcologyId::new(2, 7);
        let mut uninterrupted =
            LiveEcology::new(id, SparseStandingSurface::empty_rank(80).unwrap());
        let first_cut = relation_cut(&[13, 29, 17, 31], 71, 0);
        let open = uninterrupted
            .commit(uninterrupted.prepare(first_cut).unwrap(), 0)
            .unwrap();
        assert!(matches!(
            uninterrupted.rest_image(),
            Err(ContactCycleError::LiveInterval)
        ));
        let returned_cut = relation_cut(&[37, 41, 43], 72, 0);
        let returned = uninterrupted
            .prepare_mounted(
                returned_cut.clone(),
                &[CurrentMount::Continue(open.lineage(0).unwrap())],
            )
            .unwrap();
        let closed = uninterrupted
            .close(open, returned_cut, returned, 0, 0)
            .unwrap();
        let handle = closed.lineage(0).unwrap().durable_handle();
        let image = uninterrupted.rest_image().unwrap();
        assert_eq!(image.lineages().len(), 1);
        assert_eq!(image.lineages()[0].handle(), handle);
        let reopened = LiveEcology::from_rest_image(image).unwrap();
        assert_eq!(reopened.id(), uninterrupted.id());
        assert_eq!(reopened.generation(), uninterrupted.generation());
        assert_eq!(reopened.standing(), uninterrupted.standing());

        let later = relation_cut(&[47, 53, 59, 61], 73, 0);
        let mut expected = uninterrupted
            .prepare_mounted(
                later.clone(),
                &[CurrentMount::Continue(
                    uninterrupted.lineage(handle).unwrap(),
                )],
            )
            .unwrap();
        let mut recovered = reopened
            .prepare_mounted(
                later,
                &[CurrentMount::Continue(reopened.lineage(handle).unwrap())],
            )
            .unwrap();
        expected
            .enacted
            .prepare_cut(0, uninterrupted.standing())
            .unwrap();
        recovered
            .enacted
            .prepare_cut(0, reopened.standing())
            .unwrap();
        assert_eq!(face(&expected), face(&recovered));
        assert_eq!(expected.enacted.emissions, recovered.enacted.emissions);
        assert_eq!(
            expected.enacted.prepared_cut(0).unwrap().fold,
            recovered.enacted.prepared_cut(0).unwrap().fold
        );
        assert_eq!(
            expected.enacted.prepared_cut(0).unwrap().successor,
            recovered.enacted.prepared_cut(0).unwrap().successor
        );
    }

    #[test]
    fn a_full_checkpoint_rebinds_an_open_deed_without_replaying_contact() {
        let id = EcologyId::new(0x4348_4543, 0x4f50_454e);
        let mut uninterrupted =
            LiveEcology::new(id, SparseStandingSurface::empty_rank(80).unwrap());
        let source = relation_cut(&[13, 29, 17, 31], 701, 0);
        let open = uninterrupted
            .commit(uninterrupted.prepare(source).unwrap(), 0)
            .unwrap();
        let transition = open.transition();
        let source_handle = open.lineage(0).unwrap().durable_handle();
        let image = uninterrupted.checkpoint().unwrap();
        assert!(matches!(
            image.holon().transitions(),
            [crate::TransitionStateImage::Open(open)] if open.phase() == 3
        ));
        let mut recovered = LiveEcology::from_checkpoint(image.clone()).unwrap();
        assert_eq!(recovered.checkpoint().unwrap(), image);
        let recovered_open = recovered.open_contact(transition).unwrap();
        assert_eq!(
            recovered_open.lineage(0).unwrap().durable_handle(),
            source_handle
        );

        let returned_active = relation_cut(&[37, 41, 43], 702, 0);
        let returned = uninterrupted
            .prepare_mounted(
                returned_active.clone(),
                &[CurrentMount::Continue(open.lineage(0).unwrap())],
            )
            .unwrap();
        uninterrupted
            .close(open, returned_active.clone(), returned, 0, 0)
            .unwrap();
        let recovered_returned = recovered
            .prepare_mounted(
                returned_active.clone(),
                &[CurrentMount::Continue(recovered_open.lineage(0).unwrap())],
            )
            .unwrap();
        recovered
            .close(recovered_open, returned_active, recovered_returned, 0, 0)
            .unwrap();
        assert_eq!(
            uninterrupted.checkpoint().unwrap(),
            recovered.checkpoint().unwrap()
        );
    }

    #[test]
    fn a_full_checkpoint_preserves_closed_holon_and_claimed_ancestry() {
        let mut ecology = LiveEcology::new(
            EcologyId::new(0x4348_4543, 0x434c_4f53),
            SparseStandingSurface::empty_rank(80).unwrap(),
        );
        let source = relation_cut(&[13, 29, 17, 31], 711, 0);
        let open = ecology.commit(ecology.prepare(source).unwrap(), 0).unwrap();
        let source_handle = open.lineage(0).unwrap().durable_handle();
        let returned_active = relation_cut(&[101, 103, 107], 712, 0);
        let returned = ecology
            .prepare_mounted(
                returned_active.clone(),
                &[CurrentMount::Continue(open.lineage(0).unwrap())],
            )
            .unwrap();
        let closed = ecology
            .close(open, returned_active, returned, 0, 0)
            .unwrap();
        let returned_handle = closed.lineage(0).unwrap().durable_handle();
        assert!(ecology.lineage(source_handle).is_none());
        let image = ecology.checkpoint().unwrap();
        let recovered = LiveEcology::from_checkpoint(image.clone()).unwrap();
        assert_eq!(recovered.checkpoint().unwrap(), image);
        assert!(recovered.lineage(source_handle).is_none());
        assert_eq!(
            recovered.lineage(returned_handle).unwrap().parents(),
            &[source_handle]
        );
        assert_eq!(
            recovered.holon().settlement_header().unwrap().settlements(),
            1
        );
    }

    #[test]
    fn phase_four_and_five_checkpoints_resume_without_replaying_any_conduct() {
        let id = EcologyId::new(0x5048_4153, 0x455f_3435);
        let mut source_ecology =
            LiveEcology::new(id, SparseStandingSurface::empty_rank(80).unwrap());
        let source = relation_cut(&[13, 29, 17, 31], 721, 0);
        let open = source_ecology
            .commit(source_ecology.prepare(source).unwrap(), 0)
            .unwrap();
        let consequence = relation_cut(&[73, 79, 83], 722, 0);
        source_ecology
            .commit_consequence(&open, consequence.clone(), 0)
            .unwrap();
        assert_eq!(source_ecology.holon().phase(open.transition()), Ok(4));
        let phase_four = source_ecology.checkpoint().unwrap();

        let mut expected = LiveEcology::from_checkpoint(phase_four.clone()).unwrap();
        let mut interrupted = LiveEcology::from_checkpoint(phase_four).unwrap();
        let expected_open = expected.open_contact(open.transition()).unwrap();
        let interrupted_open = interrupted.open_contact(open.transition()).unwrap();
        let source_occurrence = first_contacted_incidence(&interrupted_open, 0);
        let plan = SettlementPlan::new(
            vec![SourceDisposition::Continued(0)],
            vec![ReturnOrigin::Continued(0)],
            vec![LineageIncidence::new(
                source_occurrence.0,
                source_occurrence.1,
                0,
                0,
            )],
        );
        let returned_active = relation_cut(&[89, 97, 101], 723, 0);
        let expected_return = expected
            .prepare_mounted(
                returned_active.clone(),
                &[CurrentMount::Continue(expected_open.lineage(0).unwrap())],
            )
            .unwrap();
        expected
            .close_resolved(
                expected_open,
                consequence.clone(),
                expected_return,
                0,
                0,
                plan.clone(),
            )
            .unwrap();

        let interrupted_return = interrupted
            .prepare_mounted(
                returned_active,
                &[CurrentMount::Continue(interrupted_open.lineage(0).unwrap())],
            )
            .unwrap();
        let pending = interrupted
            .commit_returned(interrupted_open, interrupted_return, 0, plan)
            .unwrap();
        assert_eq!(interrupted.holon().phase(pending.transition()), Ok(5));
        let phase_five = interrupted.checkpoint().unwrap();
        let mut recovered = LiveEcology::from_checkpoint(phase_five.clone()).unwrap();
        assert_eq!(recovered.checkpoint().unwrap(), phase_five);
        let recovered_pending = recovered.pending_after(pending.transition()).unwrap();
        recovered.finish_returned(recovered_pending).unwrap();
        assert_eq!(
            expected.checkpoint().unwrap(),
            recovered.checkpoint().unwrap()
        );
    }

    #[test]
    fn commit_installs_receiver_and_population_together_and_a_stale_sibling_changes_nothing() {
        let mut ecology = LiveEcology::new(
            EcologyId::new(3, 1),
            SparseStandingSurface::empty(64).unwrap(),
        );
        let active = heterogeneous_cut();
        let first = ecology.prepare(active.clone()).unwrap();
        let stale = ecology.prepare(active).unwrap();
        let open = ecology.commit(first, 0).unwrap();
        let carried = open.carried_cut();
        assert_eq!(carried.cut(), 0);
        assert_eq!(carried.incidence_count(), 2);
        assert_eq!(carried.directed(), &[DirectedIncidence::new(0, 1)]);
        let first_event = open.deed.event_surface(0).unwrap();
        assert_eq!((first_event.atom_offset(), first_event.atoms()), (0, 1));
        assert_eq!(open.deed.event_atoms(0).unwrap().len(), 1);
        assert_eq!(first_event.action(), open.deed.active.actions[0]);
        assert!(carried.incidence_surface(0).is_some());
        assert!(carried.incidence_surface(1).is_some());
        assert!(carried.incidence_surface(2).is_none());
        assert!(open.lineage(0).is_some());
        let standing = ecology.standing.clone();
        let generations = ecology.generation;
        let enacted = ecology.enacted.len();
        assert!(matches!(
            ecology.commit(stale, 0),
            Err(ContactCycleError::ReceiverChanged)
        ));
        assert_eq!(ecology.standing, standing);
        assert_eq!(ecology.generation, generations);
        assert_eq!(ecology.enacted.len(), enacted);
        assert!(!ecology.standing.cells().is_empty());
    }

    #[test]
    fn a_deep_ranked_receiver_conducts_without_a_flat_grip_projection() {
        let mut ecology = LiveEcology::new(
            EcologyId::new(3, 2),
            SparseStandingSurface::empty_rank(80).unwrap(),
        );
        assert!(ecology.standing().flat_axis().is_none());
        let prepared = ecology
            .prepare(relation_cut(&[13, 29, 17, 31], 71, 0))
            .expect("the body queries a ranked receiver by construction, not flat grip");
        assert!(!prepared.enacted.emissions().deeds.is_empty());
        let open = ecology.commit(prepared, 0).unwrap();
        assert!(open.deed.prepared_cut(0).unwrap().fold().standing_rank() >= 80);
        assert!(ecology.standing().flat_axis().is_none());
    }

    #[test]
    fn only_the_world_cut_which_actually_closed_is_prepared_and_retained() {
        let mut ecology = LiveEcology::new(
            EcologyId::new(4, 1),
            SparseStandingSurface::empty(64).unwrap(),
        );
        let prepared = ecology.prepare(two_receiving_cuts()).unwrap();
        assert!(prepared.enacted.prepared_cut(0).is_none());
        assert!(prepared.enacted.prepared_cut(1).is_none());

        let open = ecology.commit(prepared, 1).unwrap();
        assert!(open.deed.prepared_cut(0).is_none());
        assert_eq!(open.deed.prepared_cut(1).unwrap().cut(), 1);
        assert_eq!(open.carried_cut().cut(), 1);
    }

    #[test]
    fn the_actual_enactment_world_consequence_and_return_close_one_live_holon() {
        let mut ecology = LiveEcology::new(
            EcologyId::new(5, 1),
            SparseStandingSurface::empty(64).unwrap(),
        );
        let presented = relation_cut(&[13, 29, 17, 31], 11, 0);
        let prepared = ecology.prepare(presented.clone()).unwrap();
        let open = ecology.commit(prepared, 0).unwrap();
        assert_eq!(ecology.holon.phase(open.transition()), Ok(3));

        let consequence = single_relation_cut(29, 23, 0);
        let returned_cut = single_relation_cut(17, 31, 0);
        let returned = ecology
            .prepare_mounted(
                returned_cut.clone(),
                &[CurrentMount::Continue(open.lineage(0).unwrap())],
            )
            .unwrap();
        let closed = ecology
            .close(open, consequence.clone(), returned, 0, 0)
            .unwrap();
        let returned_sheet = closed.carried_cut();
        assert_eq!(returned_sheet.cut(), 0);
        assert!(Arc::ptr_eq(returned_sheet.active(), &returned_cut));
        let receipt = ecology.holon.receipt(closed.transition()).unwrap();
        let roles = [
            receipt.before_cut(),
            receipt.meeting_cut(),
            receipt.deed_cut(),
            receipt.consequence_cut(),
            receipt.return_cut(),
            receipt.after_cut(),
        ];
        let kinds: Vec<_> = roles
            .iter()
            .map(|ordinal| {
                let cut = ecology.holon.boundary_cut(*ordinal).unwrap();
                ecology.holon.surface(cut.surface()).unwrap().kind()
            })
            .collect();
        assert_eq!(
            kinds,
            vec![
                crate::LiveSurfaceKind::Standing,
                crate::LiveSurfaceKind::Active,
                crate::LiveSurfaceKind::Enacted,
                crate::LiveSurfaceKind::Active,
                crate::LiveSurfaceKind::Enacted,
                crate::LiveSurfaceKind::Standing,
            ]
        );
        let consequence_role = ecology
            .holon
            .surface(
                ecology
                    .holon
                    .boundary_cut(receipt.consequence_cut())
                    .unwrap()
                    .surface(),
            )
            .unwrap()
            .active()
            .unwrap();
        assert!(Arc::ptr_eq(consequence_role, &consequence));
        let return_role = ecology
            .holon
            .surface(
                ecology
                    .holon
                    .boundary_cut(receipt.return_cut())
                    .unwrap()
                    .surface(),
            )
            .unwrap()
            .enacted()
            .unwrap();
        assert!(Arc::ptr_eq(return_role, &closed.returned));
        assert!(Arc::ptr_eq(return_role.active(), &returned_cut));
    }

    #[test]
    fn an_unsupported_relation_founds_then_later_recurrence_rides_the_grown_locality() {
        let mut ecology = LiveEcology::new(
            EcologyId::new(6, 1),
            SparseStandingSurface::empty(64).unwrap(),
        );
        let relation = relation_cut(&[13, 29, 17, 31], 11, 0);
        let first = ecology.prepare(relation.clone()).unwrap();
        let first_kinds: Vec<_> = first
            .enacted
            .emissions
            .deeds
            .iter()
            .map(|deed| deed.kind())
            .collect();
        assert!(
            first
                .enacted
                .emissions
                .deeds
                .iter()
                .any(|deed| matches!(deed.kind(), DeedKind::FoundThis | DeedKind::FoundThat)),
            "first kinds: {first_kinds:?}"
        );
        let founding_positions: Vec<_> = first
            .enacted
            .emissions
            .deeds
            .iter()
            .filter(|deed| matches!(deed.kind(), DeedKind::FoundThis | DeedKind::FoundThat))
            .map(|deed| deed.position())
            .collect();
        let open = ecology.commit(first, 0).unwrap();
        let founding_standing = ecology.standing.clone();
        assert!(Arc::ptr_eq(
            &open.deed.prepared_cut(0).unwrap().successor,
            &founding_standing
        ));
        let founding_addresses: Vec<_> = founding_positions
            .iter()
            .map(|position| {
                crate::ChartAddress::ground(*position, founding_standing.rank()).unwrap()
            })
            .collect();

        let consequence = single_relation_cut(29, 23, 0);
        let returned_cut = single_relation_cut(17, 31, 0);
        let returned_lineage = open.lineage(0).unwrap();
        let returned = ecology
            .prepare_mounted(returned_cut, &[CurrentMount::Continue(returned_lineage)])
            .unwrap();
        let closed = ecology.close(open, consequence, returned, 0, 0).unwrap();
        let receipt = ecology.holon.receipt(closed.transition()).unwrap();
        assert_eq!(receipt.residual_incidences(), 1);
        let (residual, deed_cut) = ecology.holon.residual(receipt, 0).unwrap();
        assert_eq!(residual.configuration_incidence_offset(), 0);
        assert_eq!(residual.incidences(), 1);
        assert_eq!(
            ecology.holon.surface(deed_cut.surface()).unwrap().kind(),
            crate::LiveSurfaceKind::Enacted
        );

        let later_before = ecology.standing.clone();
        // Exact inverse-grip witness for this carried frame: this distinct later relation casts at
        // the cell founded above. It is an analogy through the lived field, not verbatim replay.
        const LATER_ANALOGOUS_RELATION: i64 = -63_245;
        let later_active = single_relation_cut(LATER_ANALOGOUS_RELATION, 47, 0);
        let later_lineage = closed.lineage(0).unwrap();
        let control = prepare_with_mounts_and_order(
            later_active.clone(),
            &SparseStandingSurface::empty(64).unwrap(),
            ecology.generation,
            &ecology.owner,
            vec![CurrentMount::Continue(later_lineage.clone())],
            [0],
        )
        .unwrap();
        let later = ecology
            .prepare_mounted(
                later_active.clone(),
                &[CurrentMount::Continue(later_lineage.clone())],
            )
            .unwrap();
        let later_kinds: Vec<_> = later
            .enacted
            .emissions
            .deeds
            .iter()
            .map(|deed| deed.kind())
            .collect();
        assert!(
            later_kinds.contains(&DeedKind::Ride),
            "later kinds: {later_kinds:?}"
        );
        let carried_founding_addresses: Vec<_> = founding_addresses
            .iter()
            .map(|address| address.zero_extend(later_before.rank()).unwrap())
            .collect();
        let ridden_deed = later
            .enacted
            .emissions
            .deeds
            .iter()
            .filter(|deed| deed.kind() == DeedKind::Ride)
            .find(|deed| {
                let Some(read) = deed.standing_read() else {
                    return false;
                };
                let address = crate::ChartAddress::ground(read.position, later_before.rank())
                    .expect("the exact standing-read position grounds at the receiver rank");
                carried_founding_addresses.contains(&address)
                    && later_before.form_at_address(&address) == read.form
                    && read.form.occupied()
            })
            .copied()
            .expect("the later RIDE names the exact earlier founded standing cell that bent it");
        let ridden_foundation = ridden_deed.standing_read().unwrap();
        assert_eq!(ridden_foundation.receiver_rank, later_before.rank());
        let ridden_address =
            crate::ChartAddress::ground(ridden_foundation.position, later_before.rank()).unwrap();
        assert_eq!(
            later_before.form_at_address(&ridden_address),
            ridden_foundation.form,
            "the outward read is the exact contemporary receiver-before form"
        );
        assert!(control
            .enacted
            .emissions
            .deeds
            .iter()
            .all(|deed| deed.standing_read().is_none()));
        assert!(
            control.enacted.emissions.deeds.iter().all(|deed| {
                deed.kind() != ridden_deed.kind()
                    || deed.position() != ridden_deed.position()
                    || deed.term() != ridden_deed.term()
            }),
            "the exact RIDE consequence disappears when only the founded standing field is removed"
        );

        // A newly occupied deep receiver address has no flat quotient.  Place the already-proven
        // exact cast at its native rank-80 address; do not confuse this with zero-extending an old
        // rank-6 founder, which lawfully occupies only the enacted zero section.
        let deep_address = crate::ChartAddress::ground(ridden_foundation.position, 80).unwrap();
        let deep_before = SparseStandingSurface::from_ranked_cells(
            80,
            vec![crate::StandingCell::new(deep_address.clone(), ridden_foundation.form).unwrap()],
        )
        .unwrap();
        let deep_control = prepare_with_mounts_and_order(
            later_active.clone(),
            &SparseStandingSurface::empty_rank(80).unwrap(),
            ecology.generation,
            &ecology.owner,
            vec![CurrentMount::Continue(later_lineage.clone())],
            [0],
        )
        .unwrap();
        let deep = prepare_with_mounts_and_order(
            later_active,
            &deep_before,
            ecology.generation,
            &ecology.owner,
            vec![CurrentMount::Continue(later_lineage)],
            [0],
        )
        .unwrap();
        let deep_ride = deep
            .enacted
            .emissions
            .deeds
            .iter()
            .filter(|deed| deed.kind() == DeedKind::Ride)
            .find_map(|deed| {
                let read = deed.standing_read()?;
                let address = crate::ChartAddress::ground(read.position, 80).ok()?;
                (address == deep_address
                    && deep_before.form_at_address(&address) == read.form
                    && read.form.occupied())
                .then_some((deed, read, address))
            })
            .expect("the occupied rank-80 terrain bends the carried lineage by exact address");
        assert!(deep_ride.1.flat_grip.is_none());
        assert_eq!(deep_ride.1.receiver_rank, 80);
        assert_eq!(deep_before.form_at_address(&deep_ride.2), deep_ride.1.form);
        assert!(deep_control
            .enacted
            .emissions
            .deeds
            .iter()
            .all(|deed| deed.standing_read().is_none()));
        assert!(deep_control.enacted.emissions.deeds.iter().all(|deed| {
            deed.kind() != deep_ride.0.kind()
                || deed.position() != deep_ride.0.position()
                || deed.term() != deep_ride.0.term()
        }));
    }
}
