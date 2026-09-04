//! Shared event-span topology and the exact sparse receiving fold.
//!
//! Accepted source deeds act once and stand in [`EmissionJournal`](crate::EmissionJournal).  This
//! layer replays each distinct current-local event span once through the ordinary REGISTER deposit
//! law, then lets every physical incidence reference that one carried surface.  A cut folds its
//! incidence population into the receiver's standing chart through `RegionalForm::integrate`.
//! Repeated incidence therefore retains physical multiplicity without re-running source action.
//!
//! Directed incidence remains the cut's ordered sheet beside this instantaneous, order-free
//! configuration product.  It is not converted into an invented regional term.  A later world
//! transport may make that hand consequential through its actual relation.

use std::vec::Vec;

use body::manifold::RankedOwnError;
use body::medium::{RegionalForm, FORM_WORDS};
#[cfg(test)]
use body::place;
use body::place::Place;
use soma_abi::active::DirectedIncidence;

use crate::growing_ranked::ExactCount;
use crate::{
    ActiveCut, CutSurfaceError, DirectedCutContact, EmissionJournal, RankedFeltSurface,
    RankedSurfaceError, SparseSurfaceError, ValidatedActiveCut,
};
use crate::{ChartAddress, ChartAddressError, SparseStandingSurface};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ActiveTopologyError {
    Cut(CutSurfaceError),
    ResourceExtent,
    ResourceReservation,
    DepositRefused,
    StandingGeometry,
    StandingChanged,
    TopologyMismatch,
    DirectedUnresolved,
    Address(ChartAddressError),
}

impl From<CutSurfaceError> for ActiveTopologyError {
    fn from(error: CutSurfaceError) -> Self {
        Self::Cut(error)
    }
}

impl From<SparseSurfaceError> for ActiveTopologyError {
    fn from(error: SparseSurfaceError) -> Self {
        match error {
            SparseSurfaceError::ResourceExtent => Self::ResourceExtent,
            SparseSurfaceError::ResourceReservation => Self::ResourceReservation,
            SparseSurfaceError::DeedExtent
            | SparseSurfaceError::InvalidEmission
            | SparseSurfaceError::Topology => Self::DepositRefused,
        }
    }
}

impl From<RankedSurfaceError> for ActiveTopologyError {
    fn from(error: RankedSurfaceError) -> Self {
        match error {
            RankedSurfaceError::DeedExtent
            | RankedSurfaceError::InvalidEmission
            | RankedSurfaceError::Topology => Self::DepositRefused,
        }
    }
}

impl From<ChartAddressError> for ActiveTopologyError {
    fn from(error: ChartAddressError) -> Self {
        Self::Address(error)
    }
}

impl From<RankedOwnError> for ActiveTopologyError {
    fn from(error: RankedOwnError) -> Self {
        match error {
            RankedOwnError::ResourceReservation => Self::ResourceReservation,
            RankedOwnError::ResourceExtent => Self::ResourceExtent,
            RankedOwnError::Geometry | RankedOwnError::Topology | RankedOwnError::Poisoned => {
                Self::TopologyMismatch
            }
        }
    }
}

/// One exact live cell of a carried event-span surface. `local_address` preserves the span's own
/// accepted ranked chart history; `position` is re-grounded only when a receiver folds the cut.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CarriedCell {
    local_address: ChartAddress,
    position: Place,
    form: RegionalForm,
}

impl CarriedCell {
    pub fn local_address(&self) -> &ChartAddress {
        &self.local_address
    }

    pub fn local_grip(&self) -> Option<u32> {
        self.local_address.try_flat_grip()
    }

    pub fn position(&self) -> Place {
        self.position
    }

    pub fn form(&self) -> RegionalForm {
        self.form
    }
}

/// One distinct current-local event span after its accepted emissions have been swept once.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CarriedSpanSurface {
    current: u64,
    event_offset: u64,
    events: u64,
    deed_offset: u64,
    deeds: u64,
    rank: u64,
    occupancy: Vec<u64>,
    releases: u64,
    narrows: u64,
    cells: Vec<CarriedCell>,
}

impl CarriedSpanSurface {
    pub fn current(&self) -> u64 {
        self.current
    }

    pub fn event_offset(&self) -> u64 {
        self.event_offset
    }

    pub fn events(&self) -> u64 {
        self.events
    }

    pub fn deed_offset(&self) -> u64 {
        self.deed_offset
    }

    pub fn deeds(&self) -> u64 {
        self.deeds
    }

    pub fn rank(&self) -> u64 {
        self.rank
    }

    pub fn flat_axis(&self) -> Option<u32> {
        (self.rank <= 16).then(|| 1u32 << self.rank)
    }

    pub fn occupancy_words(&self) -> &[u64] {
        &self.occupancy
    }

    pub fn occupancy_u64(&self) -> Option<u64> {
        match self.occupancy.as_slice() {
            [] => Some(0),
            [word] => Some(*word),
            _ => None,
        }
    }

    pub fn breath(&self) -> (u64, u64) {
        (self.releases, self.narrows)
    }

    pub fn cells(&self) -> &[CarriedCell] {
        &self.cells
    }
}

/// One changed receiver cell.  The complete contributing incidence and carried-span populations
/// remain in [`ActiveTopology`]; this row is the exact before/after face of their one product.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FoldedCell {
    address: ChartAddress,
    before: RegionalForm,
    after: RegionalForm,
}

impl FoldedCell {
    pub fn address(&self) -> &ChartAddress {
        &self.address
    }

    pub fn try_flat_grip(&self) -> Option<u32> {
        self.address.try_flat_grip()
    }

    pub fn before(&self) -> RegionalForm {
        self.before
    }

    pub fn after(&self) -> RegionalForm {
        self.after
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FoldedCut {
    cut: u64,
    standing_rank: u64,
    cells: Vec<FoldedCell>,
}

impl FoldedCut {
    pub fn cut(&self) -> u64 {
        self.cut
    }

    pub fn cells(&self) -> &[FoldedCell] {
        &self.cells
    }

    pub fn standing_rank(&self) -> u64 {
        self.standing_rank
    }

    /// Commit a previously prepared receiver fold.  The complete before-face is checked before
    /// the first write, so a changed receiver refuses without partial mutation.  Once that check
    /// closes, installing the already-carried after rows is infallible.
    pub fn commit(&self, standing: &mut [u32]) -> Result<(), ActiveTopologyError> {
        let axis = flat_axis_for_rank(self.standing_rank)?;
        standing_extent(standing, axis as i64)?;
        for cell in &self.cells {
            let grip = cell
                .try_flat_grip()
                .ok_or(ActiveTopologyError::StandingGeometry)?;
            let word = grip as usize * FORM_WORDS;
            if RegionalForm::unpack(standing, word) != cell.before {
                return Err(ActiveTopologyError::StandingChanged);
            }
        }
        for cell in &self.cells {
            let grip = cell
                .try_flat_grip()
                .ok_or(ActiveTopologyError::StandingGeometry)?;
            let word = grip as usize * FORM_WORDS;
            cell.after.pack(standing, word);
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct SpanKey {
    current: u64,
    event_offset: u64,
    events: u64,
}

fn validate_directed_contacts(
    active: ValidatedActiveCut<'_>,
    contacts: &[DirectedCutContact],
) -> Result<(), ActiveTopologyError> {
    let expected = usize::try_from(active.header.directed())
        .map_err(|_| ActiveTopologyError::ResourceExtent)?;
    if contacts.len() != expected {
        return Err(ActiveTopologyError::DirectedUnresolved);
    }
    let mut cut = 0u64;
    let mut contact = 0usize;
    while cut < active.header.cuts() {
        let span = active.cuts[cut as usize];
        let mut local = 0u64;
        while local < span.directed() {
            let directed = span
                .directed_offset()
                .checked_add(local)
                .ok_or(ActiveTopologyError::ResourceExtent)?;
            let actual = contacts
                .get(contact)
                .copied()
                .ok_or(ActiveTopologyError::DirectedUnresolved)?;
            let expected_edge = active
                .directed
                .get(usize::try_from(directed).map_err(|_| ActiveTopologyError::ResourceExtent)?)
                .copied()
                .ok_or(ActiveTopologyError::TopologyMismatch)?;
            if actual.cut() != cut
                || actual.directed() != directed
                || actual.edge() != expected_edge
                || actual.needs_resolution()
            {
                return Err(ActiveTopologyError::DirectedUnresolved);
            }
            contact += 1;
            local += 1;
        }
        cut += 1;
    }
    (contact == contacts.len())
        .then_some(())
        .ok_or(ActiveTopologyError::TopologyMismatch)
}

/// The active cut's distinct carried event-span surfaces and the plural incidence references into
/// them.  The deterministic index locates already-lived topology; it never selects contact or
/// changes a deed.
pub struct ActiveTopology<'a> {
    active: &'a ActiveCut,
    emissions: &'a EmissionJournal,
    surfaces: Vec<CarriedSpanSurface>,
    incidence_surface: Vec<usize>,
    directed_contacts: Vec<DirectedCutContact>,
}

impl<'a> ActiveTopology<'a> {
    pub fn new(
        active: &'a ActiveCut,
        emissions: &'a EmissionJournal,
    ) -> Result<Self, ActiveTopologyError> {
        if active.header.directed() != 0 {
            // A source-supplied hand cannot be silently left beside the fold. Resolving it needs
            // the target current's actual pre-event receiver, which this detached constructor does
            // not own. Production enters through the contact cycle below.
            return Err(ActiveTopologyError::DirectedUnresolved);
        }
        Self::new_validated(
            active.validated().map_err(CutSurfaceError::from)?,
            emissions,
            Vec::new(),
        )
    }

    pub(crate) fn new_validated(
        active: ValidatedActiveCut<'a>,
        emissions: &'a EmissionJournal,
        directed_contacts: Vec<DirectedCutContact>,
    ) -> Result<Self, ActiveTopologyError> {
        // Establish the active/emission relation once. Every operation below reads those immutable
        // populations directly; no current-local conductor rescans the complete cut.
        emissions
            .validate_against(active.active())
            .map_err(CutSurfaceError::from)?;
        validate_directed_contacts(active, &directed_contacts)?;

        let incidence_extent = usize::try_from(active.header.incidences())
            .map_err(|_| ActiveTopologyError::ResourceExtent)?;
        let mut keys = Vec::new();
        keys.try_reserve_exact(incidence_extent)
            .map_err(|_| ActiveTopologyError::ResourceReservation)?;
        for incidence in &active.incidences {
            keys.push(span_key(active.active(), *incidence)?);
        }
        keys.sort_unstable();
        keys.dedup();

        let mut surfaces = Vec::new();
        surfaces
            .try_reserve_exact(keys.len())
            .map_err(|_| ActiveTopologyError::ResourceReservation)?;
        for &key in &keys {
            surfaces.push(materialize_span(active.active(), emissions, key)?);
        }

        let mut incidence_surface = Vec::new();
        incidence_surface
            .try_reserve_exact(incidence_extent)
            .map_err(|_| ActiveTopologyError::ResourceReservation)?;
        for incidence in &active.incidences {
            let key = span_key(active.active(), *incidence)?;
            let surface = keys
                .binary_search(&key)
                .map_err(|_| ActiveTopologyError::TopologyMismatch)?;
            incidence_surface.push(surface);
        }
        Ok(Self {
            active: active.active(),
            emissions,
            surfaces,
            incidence_surface,
            directed_contacts,
        })
    }

    pub fn surfaces(&self) -> &[CarriedSpanSurface] {
        &self.surfaces
    }

    pub(crate) fn into_owned_parts(
        self,
    ) -> (Vec<CarriedSpanSurface>, Vec<usize>, Vec<DirectedCutContact>) {
        (
            self.surfaces,
            self.incidence_surface,
            self.directed_contacts,
        )
    }

    pub fn directed_contacts(&self) -> &[DirectedCutContact] {
        &self.directed_contacts
    }

    /// The exact once-enacted deed population from which the shared span surfaces were formed.
    /// It remains mounted beside the derived surfaces and is never flattened into new source light.
    pub fn emissions(&self) -> &EmissionJournal {
        self.emissions
    }

    pub fn surface_for_incidence(&self, incidence: u64) -> Option<&CarriedSpanSurface> {
        let surface = *self
            .incidence_surface
            .get(usize::try_from(incidence).ok()?)?;
        self.surfaces.get(surface)
    }

    pub fn surface_for_cut_incidence(
        &self,
        cut: u64,
        local: u64,
    ) -> Result<&CarriedSpanSurface, ActiveTopologyError> {
        let span = self
            .active
            .cuts
            .get(usize::try_from(cut).map_err(|_| ActiveTopologyError::ResourceExtent)?)
            .ok_or(CutSurfaceError::CutAbsent)?;
        if local >= span.incidences() {
            return Err(CutSurfaceError::HostExtent.into());
        }
        let incidence = span
            .incidence_offset()
            .checked_add(local)
            .ok_or(ActiveTopologyError::ResourceExtent)?;
        self.surface_for_incidence(incidence)
            .ok_or(ActiveTopologyError::TopologyMismatch)
    }

    pub fn directed(&self, cut: u64) -> Result<&[DirectedIncidence], ActiveTopologyError> {
        let span = self
            .active
            .cuts
            .get(usize::try_from(cut).map_err(|_| ActiveTopologyError::ResourceExtent)?)
            .ok_or(CutSurfaceError::CutAbsent)?;
        if span.directed() == 0 {
            return Ok(&[]);
        }
        let first = usize::try_from(span.directed_offset())
            .map_err(|_| ActiveTopologyError::ResourceExtent)?;
        let after = usize::try_from(
            span.directed_offset()
                .checked_add(span.directed())
                .ok_or(ActiveTopologyError::ResourceExtent)?,
        )
        .map_err(|_| ActiveTopologyError::ResourceExtent)?;
        self.active
            .directed
            .get(first..after)
            .ok_or(ActiveTopologyError::TopologyMismatch)
    }

    /// Prepare one complete sparse cut against the supplied receiver-before chart.  Only touched
    /// grips are visited.  Layout sorting groups equal grips for the order-free product; it cannot
    /// select, suppress, or serialize an incidence.  No receiver word is changed here.
    pub fn prepare_fold(
        &self,
        cut_ordinal: u64,
        standing: &[u32],
        standing_axis: i64,
    ) -> Result<FoldedCut, ActiveTopologyError> {
        let cells = standing_extent(standing, standing_axis)?;
        let standing_rank = (standing_axis as u64).trailing_zeros() as u64;
        let standing_occupancy = standing
            .chunks_exact(FORM_WORDS)
            .filter(|row| RegionalForm::unpack(row, 0).occupied())
            .count();
        self.prepare_fold_from(
            cut_ordinal,
            standing_rank,
            |address| {
                let grip = address
                    .try_flat_grip()
                    .ok_or(ActiveTopologyError::StandingGeometry)?;
                if grip as usize >= cells {
                    return Err(ActiveTopologyError::StandingGeometry);
                }
                Ok(RegionalForm::unpack(standing, grip as usize * FORM_WORDS))
            },
            false,
            standing_occupancy,
        )
    }

    /// Prepare one complete cut against sparse receiver terrain.  This is the production path;
    /// the dense method remains an exact compatibility gauge.  Both call the same integration
    /// law and produce the same `FoldedCut` before-face/after-face testimony.
    pub fn prepare_sparse_fold(
        &self,
        cut_ordinal: u64,
        standing: &SparseStandingSurface,
    ) -> Result<FoldedCut, ActiveTopologyError> {
        self.prepare_fold_from(
            cut_ordinal,
            standing.rank(),
            |address| {
                standing
                    .form_at_projected(address)
                    .map_err(|_| ActiveTopologyError::StandingGeometry)
            },
            true,
            standing.cells().len(),
        )
    }

    fn prepare_fold_from(
        &self,
        cut_ordinal: u64,
        standing_rank: u64,
        standing_at: impl FnMut(&ChartAddress) -> Result<RegionalForm, ActiveTopologyError>,
        receiver_can_rebase: bool,
        standing_occupancy: usize,
    ) -> Result<FoldedCut, ActiveTopologyError> {
        prepare_fold_from_parts(
            self.active,
            &self.surfaces,
            &self.incidence_surface,
            &self.directed_contacts,
            cut_ordinal,
            standing_rank,
            standing_at,
            receiver_can_rebase,
            standing_occupancy,
        )
    }

    /// Compatibility convenience for callers which can commit immediately.  Preparation still
    /// completes in full before the receiver is touched.
    pub fn fold_cut(
        &self,
        cut_ordinal: u64,
        standing: &mut [u32],
        standing_axis: i64,
    ) -> Result<FoldedCut, ActiveTopologyError> {
        let folded = self.prepare_fold(cut_ordinal, standing, standing_axis)?;
        folded.commit(standing)?;
        Ok(folded)
    }
}

/// Prepare the one cut which actually closed after the borrowed topology owner has dissipated.
/// The carried surfaces are the once-enacted population produced by [`ActiveTopology`]; this path
/// never replays source deeds or prepares sibling cuts which did not occur.
pub(crate) fn prepare_sparse_fold_from_owned(
    active: &ActiveCut,
    surfaces: &[CarriedSpanSurface],
    incidence_surface: &[usize],
    directed_contacts: &[DirectedCutContact],
    cut_ordinal: u64,
    standing: &SparseStandingSurface,
) -> Result<FoldedCut, ActiveTopologyError> {
    prepare_fold_from_parts(
        active,
        surfaces,
        incidence_surface,
        directed_contacts,
        cut_ordinal,
        standing.rank(),
        |address| {
            standing
                .form_at_projected(address)
                .map_err(|_| ActiveTopologyError::StandingGeometry)
        },
        true,
        standing.cells().len(),
    )
}

fn prepare_fold_from_parts(
    active: &ActiveCut,
    surfaces: &[CarriedSpanSurface],
    incidence_surface: &[usize],
    directed_contacts: &[DirectedCutContact],
    cut_ordinal: u64,
    standing_rank: u64,
    mut standing_at: impl FnMut(&ChartAddress) -> Result<RegionalForm, ActiveTopologyError>,
    receiver_can_rebase: bool,
    standing_occupancy: usize,
) -> Result<FoldedCut, ActiveTopologyError> {
    let cut = active
        .cuts
        .get(usize::try_from(cut_ordinal).map_err(|_| ActiveTopologyError::ResourceExtent)?)
        .ok_or(CutSurfaceError::CutAbsent)?;
    let surface_for_local = |local: u64| -> Result<&CarriedSpanSurface, ActiveTopologyError> {
        if local >= cut.incidences() {
            return Err(ActiveTopologyError::TopologyMismatch);
        }
        let incidence = cut
            .incidence_offset()
            .checked_add(local)
            .ok_or(ActiveTopologyError::ResourceExtent)?;
        let surface = *incidence_surface
            .get(usize::try_from(incidence).map_err(|_| ActiveTopologyError::ResourceExtent)?)
            .ok_or(ActiveTopologyError::TopologyMismatch)?;
        surfaces
            .get(surface)
            .ok_or(ActiveTopologyError::TopologyMismatch)
    };

    let mut contribution_count = 0usize;
    let mut local = 0u64;
    while local < cut.incidences() {
        contribution_count = contribution_count
            .checked_add(surface_for_local(local)?.cells.len())
            .ok_or(ActiveTopologyError::ResourceExtent)?;
        local += 1;
    }
    contribution_count = contribution_count
        .checked_add(
            directed_contacts
                .iter()
                .filter(|contact| contact.cut() == cut_ordinal && contact.emission().is_some())
                .count(),
        )
        .ok_or(ActiveTopologyError::ResourceExtent)?;
    let mut source_contributions = Vec::new();
    source_contributions
        .try_reserve_exact(contribution_count)
        .map_err(|_| ActiveTopologyError::ResourceReservation)?;
    local = 0;
    while local < cut.incidences() {
        for cell in &surface_for_local(local)?.cells {
            source_contributions.push((cell.position, cell.form));
        }
        local += 1;
    }
    for contact in directed_contacts
        .iter()
        .copied()
        .filter(|contact| contact.cut() == cut_ordinal)
    {
        let Some(emission) = contact.emission() else {
            continue;
        };
        if !emission.hand_is_exact() {
            return Err(ActiveTopologyError::TopologyMismatch);
        }
        source_contributions.push((
            emission.position,
            RegionalForm::UNBORN.deposit(emission.term),
        ));
    }

    // The receiver's grain changes only when the exact population of genuinely new addresses
    // carries into its current chart hand.  Each candidate rank is a complete retry from the same
    // immutable before-face; no intermediate chart or partial fold becomes visible.
    let mut accepted_rank = standing_rank;
    if receiver_can_rebase {
        loop {
            let mut distinct = Vec::new();
            distinct
                .try_reserve_exact(source_contributions.len())
                .map_err(|_| ActiveTopologyError::ResourceReservation)?;
            for (position, _) in &source_contributions {
                distinct.push(ChartAddress::ground(*position, accepted_rank)?);
            }
            distinct.sort_unstable();
            distinct.dedup();

            let mut occupancy = ExactCount::from_usize(standing_occupancy);
            let mut carried = false;
            for address in &distinct {
                if standing_at(address)?.occupied() {
                    continue;
                }
                let after = occupancy.incremented()?;
                let tooth = if accepted_rank == 0 {
                    0
                } else {
                    accepted_rank
                        .checked_mul(2)
                        .and_then(|value| value.checked_sub(1))
                        .ok_or(ActiveTopologyError::ResourceExtent)?
                };
                carried |= occupancy.entered_bit(&after, tooth)?;
                occupancy = after;
            }
            if !carried {
                break;
            }
            accepted_rank = accepted_rank
                .checked_add(1)
                .ok_or(ActiveTopologyError::ResourceExtent)?;
        }
    }

    let mut contributions = Vec::new();
    contributions
        .try_reserve_exact(source_contributions.len())
        .map_err(|_| ActiveTopologyError::ResourceReservation)?;
    for (position, form) in source_contributions {
        let address = ChartAddress::ground(position, accepted_rank)?;
        standing_at(&address)?;
        contributions.push((address, form));
    }
    contributions.sort_unstable_by(|left, right| left.0.cmp(&right.0));

    let mut folded = Vec::new();
    folded
        .try_reserve_exact(contributions.len())
        .map_err(|_| ActiveTopologyError::ResourceReservation)?;
    let mut forms = Vec::new();
    forms
        .try_reserve_exact(contributions.len().saturating_add(1))
        .map_err(|_| ActiveTopologyError::ResourceReservation)?;
    let mut at = 0usize;
    while at < contributions.len() {
        let address = contributions[at].0.clone();
        let before = standing_at(&address)?;
        forms.clear();
        forms.push(before);
        while at < contributions.len() && contributions[at].0 == address {
            forms.push(contributions[at].1);
            at += 1;
        }
        let after = body::medium::integrate(&forms).occupy();
        folded.push(FoldedCell {
            address,
            before,
            after,
        });
    }
    Ok(FoldedCut {
        cut: cut_ordinal,
        standing_rank: accepted_rank,
        cells: folded,
    })
}

fn span_key(
    active: &ActiveCut,
    incidence: soma_abi::active::Incidence,
) -> Result<SpanKey, ActiveTopologyError> {
    let current = active
        .currents
        .get(
            usize::try_from(incidence.current())
                .map_err(|_| ActiveTopologyError::ResourceExtent)?,
        )
        .ok_or(ActiveTopologyError::TopologyMismatch)?;
    Ok(SpanKey {
        current: incidence.current(),
        event_offset: current
            .event_offset()
            .checked_add(incidence.current_event_offset())
            .ok_or(ActiveTopologyError::ResourceExtent)?,
        events: incidence.current_events(),
    })
}

fn materialize_span(
    _active: &ActiveCut,
    emissions: &EmissionJournal,
    key: SpanKey,
) -> Result<CarriedSpanSurface, ActiveTopologyError> {
    let after_event = key
        .event_offset
        .checked_add(key.events)
        .ok_or(ActiveTopologyError::ResourceExtent)?;
    let first_event = emissions
        .events
        .get(usize::try_from(key.event_offset).map_err(|_| ActiveTopologyError::ResourceExtent)?)
        .ok_or(ActiveTopologyError::TopologyMismatch)?;
    let last_event = emissions
        .events
        .get(usize::try_from(after_event - 1).map_err(|_| ActiveTopologyError::ResourceExtent)?)
        .ok_or(ActiveTopologyError::TopologyMismatch)?;
    let deed_offset = first_event.deed_offset();
    let after_deed = last_event
        .deed_offset()
        .checked_add(last_event.deeds())
        .ok_or(ActiveTopologyError::ResourceExtent)?;
    let deed_first =
        usize::try_from(deed_offset).map_err(|_| ActiveTopologyError::ResourceExtent)?;
    let deed_after =
        usize::try_from(after_deed).map_err(|_| ActiveTopologyError::ResourceExtent)?;
    let deeds = emissions
        .deeds
        .get(deed_first..deed_after)
        .ok_or(ActiveTopologyError::TopologyMismatch)?;
    let mut surface = RankedFeltSurface::preflight(deeds.len())?;
    for deed in deeds {
        surface.deposit(deed.felt_emission())?;
    }
    let rank = surface.rank();
    let mut occupancy = Vec::new();
    occupancy
        .try_reserve_exact(surface.occupancy_words().len())
        .map_err(|_| ActiveTopologyError::ResourceReservation)?;
    occupancy.extend_from_slice(surface.occupancy_words());
    let (releases, narrows) = surface.breath();
    let mut cells = Vec::new();
    cells
        .try_reserve_exact(surface.cells().len())
        .map_err(|_| ActiveTopologyError::ResourceReservation)?;
    for sparse in surface.cells() {
        if !sparse.form().occupied() {
            return Err(ActiveTopologyError::TopologyMismatch);
        }
        cells.push(CarriedCell {
            local_address: sparse.address().clone(),
            position: sparse.founder(),
            form: sparse.form(),
        });
    }
    Ok(CarriedSpanSurface {
        current: key.current,
        event_offset: key.event_offset,
        events: key.events,
        deed_offset,
        deeds: after_deed - deed_offset,
        rank,
        occupancy,
        releases,
        narrows,
        cells,
    })
}

fn flat_axis_for_rank(rank: u64) -> Result<u32, ActiveTopologyError> {
    if rank > 16 {
        return Err(ActiveTopologyError::StandingGeometry);
    }
    Ok(1u32 << rank)
}

fn standing_extent(standing: &[u32], standing_axis: i64) -> Result<usize, ActiveTopologyError> {
    if standing_axis <= 0
        || standing_axis & (standing_axis - 1) != 0
        || standing_axis > u32::MAX as i64
    {
        return Err(ActiveTopologyError::StandingGeometry);
    }
    let axis = usize::try_from(standing_axis).map_err(|_| ActiveTopologyError::StandingGeometry)?;
    let cells = axis
        .checked_mul(axis)
        .ok_or(ActiveTopologyError::StandingGeometry)?;
    let words = cells
        .checked_mul(FORM_WORDS)
        .ok_or(ActiveTopologyError::StandingGeometry)?;
    if standing.len() != words {
        return Err(ActiveTopologyError::StandingGeometry);
    }
    Ok(cells)
}

#[cfg(test)]
mod tests {
    use super::*;
    use body::channel::WindingQuantum;
    use body::manifold::{
        atom_node, narrow_own_cells, own_cell_position, zero_extend_own_cells, ErosBody, FeltDeed,
        FeltEmission, OwnRecast, SparseOwnCell, ENCLOSURE_WORDS, OWN_CELL_FORM, OWN_CELL_LIVE,
        OWN_CELL_WORDS,
    };
    use body::medium::FeltTerm;
    use body::num::Cog;
    use body::soul::Chi;
    use soma_abi::active::{
        ActionCurrent, CurrentSpan, CutSpan, EventSpan, Incidence, OriginRef, RelationAtom,
    };
    use soma_abi::emission::{CurrentEmissionSpan, DeedEmission, EventEmissionSpan, Header};

    struct ExactChart {
        words: Vec<u32>,
    }

    impl ExactChart {
        fn born() -> Self {
            Self {
                words: vec![0u32; OWN_CELL_WORDS],
            }
        }
    }

    impl OwnRecast for ExactChart {
        fn words(&self) -> &[u32] {
            &self.words
        }

        fn words_mut(&mut self) -> &mut [u32] {
            &mut self.words
        }

        fn recast(&mut self, old_axis: i64, new_axis: i64) {
            let mut fresh = vec![0u32; new_axis as usize * new_axis as usize * OWN_CELL_WORDS];
            if new_axis > old_axis {
                zero_extend_own_cells(&self.words, &mut fresh, old_axis, new_axis);
            } else {
                narrow_own_cells(&self.words, &mut fresh, old_axis, new_axis);
            }
            self.words = fresh;
        }
    }

    fn fixture(directed_hand: Option<bool>) -> (ActiveCut, EmissionJournal) {
        let cuts = if directed_hand.is_some() {
            vec![
                CutSpan::new(0, 3, 0, 1).unwrap(),
                CutSpan::new(3, 2, 1, 1).unwrap(),
            ]
        } else {
            vec![
                CutSpan::new(0, 3, 0, 0).unwrap(),
                CutSpan::new(3, 2, 0, 0).unwrap(),
            ]
        };
        let directed = directed_hand.map_or_else(Vec::new, |reverse| {
            vec![
                if reverse {
                    DirectedIncidence::new(2, 0)
                } else {
                    DirectedIncidence::new(0, 2)
                },
                DirectedIncidence::new(3, 4),
            ]
        });
        let active = ActiveCut::new(
            vec![
                RelationAtom::new(Cog::lit(2)).unwrap(),
                RelationAtom::new(Cog::lit(3)).unwrap(),
            ],
            vec![EventSpan::new(0, 1).unwrap(), EventSpan::new(1, 1).unwrap()],
            vec![
                ActionCurrent::new(Cog::lit(5)).unwrap(),
                ActionCurrent::new(Cog::lit(7)).unwrap(),
            ],
            vec![OriginRef::new(1, 0), OriginRef::new(2, 0)],
            vec![
                CurrentSpan::new(0, 1, 0, 1).unwrap(),
                CurrentSpan::new(1, 1, 1, 1).unwrap(),
            ],
            cuts,
            vec![
                Incidence::new(0, 0, 1).unwrap(),
                Incidence::new(0, 0, 1).unwrap(),
                Incidence::new(1, 0, 1).unwrap(),
                Incidence::new(1, 0, 1).unwrap(),
                Incidence::new(0, 0, 1).unwrap(),
            ],
            directed,
        )
        .unwrap();
        let deed = |value| {
            DeedEmission::new(
                FeltEmission {
                    position: place::origin(),
                    term: FeltTerm {
                        chi: Chi {
                            same: Cog::lit(value),
                            other: Cog::ZERO,
                        },
                        winding: WindingQuantum::None,
                    },
                    deed: FeltDeed::Ride,
                    standing_read: None,
                },
                0,
                1,
            )
            .unwrap()
        };
        let journal = EmissionJournal {
            header: Header::new(2, 2, 2).unwrap(),
            events: vec![
                EventEmissionSpan::new(0, 1).unwrap(),
                EventEmissionSpan::new(1, 1).unwrap(),
            ],
            deeds: vec![deed(5), deed(7)],
            currents: vec![
                CurrentEmissionSpan::new(0, 1, 0, 1).unwrap(),
                CurrentEmissionSpan::new(1, 1, 1, 1).unwrap(),
            ],
        };
        journal.validate_against(&active).unwrap();
        (active, journal)
    }

    #[test]
    fn distinct_spans_materialize_once_and_plural_incidence_reuses_them() {
        let (active, journal) = fixture(None);
        let topology = ActiveTopology::new(&active, &journal).unwrap();
        assert_eq!(topology.surfaces().len(), 2);
        assert!(std::ptr::eq(
            topology.surface_for_cut_incidence(0, 0).unwrap(),
            topology.surface_for_cut_incidence(0, 1).unwrap(),
        ));
        assert!(std::ptr::eq(
            topology.surface_for_cut_incidence(0, 0).unwrap(),
            topology.surface_for_cut_incidence(1, 1).unwrap(),
        ));
    }

    #[test]
    fn incidence_multiplicity_changes_the_product_without_replaying_a_deed() {
        let (active, journal) = fixture(None);
        let topology = ActiveTopology::new(&active, &journal).unwrap();
        let mut plural = vec![0u32; 4 * FORM_WORDS];
        let mut singular = plural.clone();
        let plural_fold = topology.fold_cut(0, &mut plural, 2).unwrap();
        let singular_fold = topology.fold_cut(1, &mut singular, 2).unwrap();
        assert_eq!(plural_fold.cells().len(), 1);
        assert_eq!(singular_fold.cells().len(), 1);
        assert_ne!(plural, singular);

        let expected_plural = body::medium::integrate(&[
            RegionalForm::UNBORN,
            RegionalForm::UNBORN.deposit(journal.deeds[0].term()),
            RegionalForm::UNBORN.deposit(journal.deeds[0].term()),
            RegionalForm::UNBORN.deposit(journal.deeds[1].term()),
        ])
        .occupy();
        assert_eq!(plural_fold.cells()[0].after(), expected_plural);
        assert_eq!(
            journal.deeds.len(),
            2,
            "source deeds still stand exactly once"
        );
    }

    #[test]
    fn a_prepared_fold_never_mutates_and_a_changed_receiver_refuses_whole() {
        let (active, journal) = fixture(None);
        let topology = ActiveTopology::new(&active, &journal).unwrap();
        let mut standing = vec![0u32; 4 * FORM_WORDS];
        let before = standing.clone();
        let prepared = topology.prepare_fold(0, &standing, 2).unwrap();
        assert_eq!(standing, before);

        let changed = RegionalForm::UNBORN.deposit(FeltTerm {
            chi: Chi {
                same: Cog::lit(101),
                other: Cog::ZERO,
            },
            winding: WindingQuantum::None,
        });
        changed.pack(
            &mut standing,
            prepared.cells()[0].try_flat_grip().unwrap() as usize * FORM_WORDS,
        );
        let changed_before_commit = standing.clone();
        assert_eq!(
            prepared.commit(&mut standing),
            Err(ActiveTopologyError::StandingChanged)
        );
        assert_eq!(standing, changed_before_commit);

        standing = before.clone();
        prepared.commit(&mut standing).unwrap();
        assert_ne!(standing, before);
    }

    #[test]
    fn sparse_receiver_successor_is_dense_exact_and_never_mutates_its_before_face() {
        let (active, journal) = fixture(None);
        let topology = ActiveTopology::new(&active, &journal).unwrap();

        let mut dense = vec![0u32; 4 * FORM_WORDS];
        let dense_fold = topology.fold_cut(0, &mut dense, 2).unwrap();

        let sparse = crate::SparseStandingSurface::empty(2).unwrap();
        let before = sparse.clone();
        let sparse_fold = topology.prepare_sparse_fold(0, &sparse).unwrap();
        assert_eq!(sparse_fold, dense_fold);
        let successor = sparse.prepare_successor(&sparse_fold).unwrap();
        assert_eq!(sparse, before);

        let mut expected = Vec::new();
        for grip in 0..4u32 {
            let form = RegionalForm::unpack(&dense, grip as usize * FORM_WORDS);
            if form.occupied() {
                expected.push(body::manifold::SparseStandingCell::new(grip, form).unwrap());
            }
        }
        assert_eq!(successor.flat_cells().unwrap(), expected);
    }

    #[test]
    fn the_sparse_receiver_digit_is_caused_by_the_arriving_population() {
        let (active, journal) = fixture(None);
        let topology = ActiveTopology::new(&active, &journal).unwrap();
        let standing = crate::SparseStandingSurface::empty_rank(0).unwrap();

        let folded = topology.prepare_sparse_fold(0, &standing).unwrap();
        assert_eq!(folded.standing_rank(), 1);
        assert_eq!(standing.rank(), 0, "preparation cannot mutate the receiver");

        let successor = standing.prepare_successor(&folded).unwrap();
        assert_eq!(successor.rank(), 1);
        assert_eq!(successor.flat_axis(), Some(2));
        assert_eq!(successor.cells().len(), 1);
    }

    #[test]
    fn ranked_receiver_carry_is_the_flat_chart_law_at_every_shared_rank() {
        for rank in 0..=16u64 {
            let axis = 1u32 << rank;
            let hand = body::chart::hand(axis);
            for before in [hand.saturating_sub(1), hand, hand.saturating_add(3)] {
                let Some(after) = before.checked_add(1) else {
                    continue;
                };
                let before_count = ExactCount::from_usize(before as usize);
                let after_count = ExactCount::from_usize(after as usize);
                let tooth = if rank == 0 { 0 } else { 2 * rank - 1 };
                assert_eq!(
                    before_count.entered_bit(&after_count, tooth).unwrap(),
                    body::chart::carried_into_hand(before, after, axis)
                );
            }
        }
    }

    #[test]
    fn directed_hand_cannot_be_silently_omitted_by_a_detached_fold() {
        let (forward_active, forward_journal) = fixture(Some(false));
        let (reverse_active, reverse_journal) = fixture(Some(true));
        assert!(matches!(
            ActiveTopology::new(&forward_active, &forward_journal),
            Err(ActiveTopologyError::DirectedUnresolved)
        ));
        assert!(matches!(
            ActiveTopology::new(&reverse_active, &reverse_journal),
            Err(ActiveTopologyError::DirectedUnresolved)
        ));
    }

    #[test]
    fn a_real_current_surface_matches_the_production_register_without_a_dense_read() {
        let relations = [
            Cog::lit(3),
            Cog::lit(-5),
            Cog::lit(8),
            Cog::lit(13),
            Cog::lit(-21),
            Cog::lit(34),
            Cog::lit(-55),
            Cog::lit(89),
            Cog::lit(-144),
            Cog::lit(233),
        ];
        let atoms: Vec<_> = relations
            .iter()
            .copied()
            .map(|relation| RelationAtom::new(relation).unwrap())
            .collect();
        let events: Vec<_> = (0..relations.len())
            .map(|ordinal| EventSpan::new(ordinal as u64, 1).unwrap())
            .collect();
        let active = ActiveCut::new(
            atoms,
            events,
            vec![ActionCurrent::new(Cog::lit(1)).unwrap(); relations.len()],
            (0..relations.len())
                .map(|ordinal| OriginRef::new(1, ordinal as u64))
                .collect(),
            vec![CurrentSpan::new(0, relations.len() as u64, 0, relations.len() as u64).unwrap()],
            vec![CutSpan::new(0, 1, 0, 0).unwrap()],
            vec![Incidence::new(0, 0, relations.len() as u64).unwrap()],
            Vec::new(),
        )
        .unwrap();

        let standing = vec![0u32; 64 * 64 * FORM_WORDS];
        let mut exact = ExactChart::born();
        let mut carrier = vec![0u32; 8 * ENCLOSURE_WORDS];
        let maximum_deeds = crate::preflight_active_deeds(&active, 8).unwrap();
        let mut builder = crate::EmissionJournalBuilder::preflight(&active, maximum_deeds).unwrap();
        let exact_face = {
            let mut body =
                ErosBody::over_register(&standing, &mut exact, 64, b"  ", 20, &mut carrier);
            crate::conduct_current_emitting(&active, 0, &mut body, &mut builder, |_| {}).unwrap();
            (body.own_axis() as u32, body.own_occupancy(), body.breath())
        };
        let journal = builder.finish(&active).unwrap();
        assert!(journal.header.deeds() <= maximum_deeds);

        let mut sparse_cells = vec![SparseOwnCell::EMPTY; maximum_deeds as usize];
        let mut sparse_carrier = vec![0u32; 8 * ENCLOSURE_WORDS];
        let mut sparse_builder =
            crate::EmissionJournalBuilder::preflight(&active, maximum_deeds).unwrap();
        let sparse_face = {
            let mut body = ErosBody::over_sparse_from_first_difference(
                &standing,
                &mut sparse_cells,
                64,
                atom_node(Cog::ZERO).place,
                &mut sparse_carrier,
            )
            .unwrap();
            crate::conduct_current_emitting(&active, 0, &mut body, &mut sparse_builder, |_| {})
                .unwrap();
            (body.own_axis() as u32, body.own_occupancy(), body.breath())
        };
        assert_eq!(sparse_face, exact_face);
        assert_eq!(sparse_builder.finish(&active).unwrap(), journal);

        let topology = ActiveTopology::new(&active, &journal).unwrap();
        let carried = &topology.surfaces()[0];
        assert_eq!(
            (
                carried.flat_axis().unwrap(),
                carried.occupancy_u64().unwrap(),
                carried.breath()
            ),
            exact_face,
        );

        let mut expected = Vec::new();
        let exact_cells = exact_face.0 as usize * exact_face.0 as usize;
        for local_grip in 0..exact_cells {
            let at = local_grip * OWN_CELL_WORDS;
            if exact.words[at + OWN_CELL_LIVE] != 0 {
                expected.push(CarriedCell {
                    local_address: ChartAddress::from_flat_grip(local_grip as u32, exact_face.0)
                        .unwrap(),
                    position: own_cell_position(&exact.words, at),
                    form: RegionalForm::unpack(&exact.words, at + OWN_CELL_FORM),
                });
            }
        }
        assert_eq!(carried.cells(), expected);
    }
}
