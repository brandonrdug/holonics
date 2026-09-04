//! Live six-role Holon continuity over mounted active-cut surfaces.
//!
//! A transition remains open while the world interval is unresolved.  Roles append only when the
//! corresponding cut actually exists; closure creates the ordinary ABI receipt in lived order.
//! Mounted surfaces remain shared active constructions rather than being flattened or reconstructed
//! from their durable wire.

use std::sync::Arc;

use soma_abi::emission::DeedKind;
use soma_abi::holon::{
    BoundaryCut, LineageIncidenceRow, ResidualIncidence, ResidualSpan, ReturnOriginRow,
    SettlementHeader, SettlementSpan, SilentReceipt, SourceDispositionRow, TransitionReceipt,
};

use crate::active_cut::{ActiveCut, ActiveCutError};
use crate::active_topology::prepare_sparse_fold_from_owned;
use crate::{
    EnactedPopulation, HolonSurfaceImage, LiveHolonImage, OpenTransitionImage,
    ProvisionalSettlementImage, SparseStandingSurface, TransitionStateImage,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SurfaceId(u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CutRef(BoundaryCut);

impl CutRef {
    pub fn surface(self) -> SurfaceId {
        SurfaceId(self.0.body())
    }

    pub fn cut(self) -> u64 {
        self.0.cut()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TransitionId(usize);

impl TransitionId {
    pub fn ordinal(self) -> u64 {
        u64::try_from(self.0).expect("a live transition ordinal fits the ABI extent")
    }

    pub fn from_ordinal(ordinal: u64) -> Result<Self, HolonError> {
        Ok(Self(
            usize::try_from(ordinal).map_err(|_| HolonError::PopulationOverflow)?,
        ))
    }
}

/// Exact committed lifecycle state of one world interval.  This is an addressable recovery face,
/// not a command to advance the interval.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TransitionStatus {
    Open(u8),
    Returned,
    Silent,
}

/// One settlement and the exact companion populations owned by this Holon.
///
/// A bare [`SettlementSpan`] is an allocation-free ABI coordinate and may arrive from an
/// untrusted checkpoint or substrate mirror. It is therefore never accepted as authority to index
/// a live Holon's populations. This view exists only after the Holon resolves its own ordinal.
#[derive(Clone, Copy, Debug)]
pub struct SettlementView<'a> {
    span: SettlementSpan,
    sources: &'a [SourceDispositionRow],
    origins: &'a [ReturnOriginRow],
    lineages: &'a [LineageIncidenceRow],
}

impl<'a> SettlementView<'a> {
    pub fn span(self) -> SettlementSpan {
        self.span
    }

    pub fn sources(self) -> &'a [SourceDispositionRow] {
        self.sources
    }

    pub fn origins(self) -> &'a [ReturnOriginRow] {
        self.origins
    }

    pub fn lineages(self) -> &'a [LineageIncidenceRow] {
        self.lineages
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HolonError {
    SurfaceAbsent,
    CutAbsent,
    TransitionAbsent,
    TransitionClosed,
    LiveInterval,
    WrongPhase { expected: u8, actual: u8 },
    ResidualAbsent,
    SettlementAbsent,
    PopulationOverflow,
    PopulationReservation,
    SurfaceInvalid(ActiveCutError),
    RecoveryInvalid,
}

/// The three source-neutral surfaces which can actually occupy a live boundary role.
///
/// `Active` is the relation population exposed by an organ. `Standing` is Soma's exact receiver
/// terrain at one side of a transition. `Enacted` retains the presented cut together with every
/// accepted deed, carried incidence surface, current-local body, and prepared receiving fold.
/// World material does not enter this enum: its organ retains that material and exposes its
/// consequence as another `ActiveCut` with opaque occurrence provenance.
pub enum LiveSurface {
    Active(Arc<ActiveCut>),
    Standing(Arc<SparseStandingSurface>),
    Enacted(Arc<EnactedPopulation>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LiveSurfaceKind {
    Active,
    Standing,
    Enacted,
}

impl LiveSurface {
    fn cuts(&self) -> u64 {
        match self {
            Self::Active(active) => active.header.cuts(),
            Self::Standing(_) => 1,
            Self::Enacted(enacted) => enacted.active().header.cuts(),
        }
    }

    fn incidences(&self, cut: usize) -> Option<u64> {
        match self {
            Self::Active(active) => active.cuts.get(cut).map(|span| span.incidences()),
            Self::Enacted(enacted) => enacted.active().cuts.get(cut).map(|span| span.incidences()),
            Self::Standing(_) => None,
        }
    }

    pub fn kind(&self) -> LiveSurfaceKind {
        match self {
            Self::Active(_) => LiveSurfaceKind::Active,
            Self::Standing(_) => LiveSurfaceKind::Standing,
            Self::Enacted(_) => LiveSurfaceKind::Enacted,
        }
    }

    pub fn active(&self) -> Option<&Arc<ActiveCut>> {
        match self {
            Self::Active(active) => Some(active),
            _ => None,
        }
    }

    pub fn standing(&self) -> Option<&Arc<SparseStandingSurface>> {
        match self {
            Self::Standing(standing) => Some(standing),
            _ => None,
        }
    }

    pub fn enacted(&self) -> Option<&Arc<EnactedPopulation>> {
        match self {
            Self::Enacted(enacted) => Some(enacted),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum TransitionState {
    Open(OpenTransition),
    Closed {
        receipt: u64,
        settlement: Option<u64>,
    },
    SettledSilent {
        receipt: u64,
        settlement: u64,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct OpenTransition {
    /// Cut-population ordinals. Only `0..phase` have been lived.
    roles: [u64; 6],
    /// Number of lived roles in `roles`; birth installs only `before`, so this begins at one.
    phase: u8,
    residual_incidence_offset: u64,
    residual_incidences: u64,
    /// Settlement populations committed with the returned role at phase five. They remain
    /// provisional until the owner installs the after-body and closes the receipt.
    provisional: Option<ProvisionalSettlement>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ProvisionalSettlement {
    source_offset: u64,
    sources: u64,
    origin_offset: u64,
    origins: u64,
    lineage_offset: u64,
    lineages: u64,
}

/// The active receiver-relative sweep.  This is runtime ecology, not a post-hoc observer record.
pub struct LiveHolon {
    surfaces: Vec<LiveSurface>,
    cuts: Vec<BoundaryCut>,
    transitions: Vec<TransitionState>,
    receipts: Vec<TransitionReceipt>,
    silent_receipts: Vec<SilentReceipt>,
    settlements: Vec<SettlementSpan>,
    source_dispositions: Vec<SourceDispositionRow>,
    return_origins: Vec<ReturnOriginRow>,
    lineage_incidences: Vec<LineageIncidenceRow>,
    residuals: Vec<ResidualSpan>,
    residual_incidences: Vec<ResidualIncidence>,
}

impl LiveHolon {
    pub fn new() -> Self {
        Self {
            surfaces: Vec::new(),
            cuts: Vec::new(),
            transitions: Vec::new(),
            receipts: Vec::new(),
            silent_receipts: Vec::new(),
            settlements: Vec::new(),
            source_dispositions: Vec::new(),
            return_origins: Vec::new(),
            lineage_incidences: Vec::new(),
            residuals: Vec::new(),
            residual_incidences: Vec::new(),
        }
    }

    /// Exact count of world intervals whose six-role sweep has not yet closed. This is a recovery
    /// boundary read only; it never advances or selects a transition.
    pub fn open_transitions(&self) -> usize {
        self.transitions
            .iter()
            .filter(|transition| matches!(transition, TransitionState::Open(_)))
            .count()
    }

    /// Reserve a complete forthcoming live interval before its first role is mounted.  The counts
    /// are physical population extents, not policy: one transition needs six cut rows and one
    /// receipt, while each retained residual needs one additional cut, span, and incidence row.
    pub fn preflight(
        &mut self,
        additional_surfaces: usize,
        additional_transitions: usize,
        additional_residuals: usize,
    ) -> Result<(), HolonError> {
        let cuts = additional_transitions
            .checked_mul(6)
            .and_then(|cuts| cuts.checked_add(additional_residuals))
            .ok_or(HolonError::PopulationOverflow)?;
        self.surfaces
            .try_reserve_exact(additional_surfaces)
            .map_err(|_| HolonError::PopulationReservation)?;
        self.cuts
            .try_reserve_exact(cuts)
            .map_err(|_| HolonError::PopulationReservation)?;
        self.transitions
            .try_reserve_exact(additional_transitions)
            .map_err(|_| HolonError::PopulationReservation)?;
        self.receipts
            .try_reserve_exact(additional_transitions)
            .map_err(|_| HolonError::PopulationReservation)?;
        self.silent_receipts
            .try_reserve_exact(additional_transitions)
            .map_err(|_| HolonError::PopulationReservation)?;
        self.residuals
            .try_reserve_exact(additional_residuals)
            .map_err(|_| HolonError::PopulationReservation)?;
        self.residual_incidences
            .try_reserve_exact(additional_residuals)
            .map_err(|_| HolonError::PopulationReservation)?;
        Ok(())
    }

    fn preflight_populations(
        &mut self,
        additional_surfaces: usize,
        additional_cuts: usize,
        additional_transitions: usize,
        additional_receipts: usize,
        additional_silent_receipts: usize,
        additional_residuals: usize,
    ) -> Result<(), HolonError> {
        self.surfaces
            .try_reserve_exact(additional_surfaces)
            .map_err(|_| HolonError::PopulationReservation)?;
        self.cuts
            .try_reserve_exact(additional_cuts)
            .map_err(|_| HolonError::PopulationReservation)?;
        self.transitions
            .try_reserve_exact(additional_transitions)
            .map_err(|_| HolonError::PopulationReservation)?;
        self.receipts
            .try_reserve_exact(additional_receipts)
            .map_err(|_| HolonError::PopulationReservation)?;
        self.silent_receipts
            .try_reserve_exact(additional_silent_receipts)
            .map_err(|_| HolonError::PopulationReservation)?;
        self.residuals
            .try_reserve_exact(additional_residuals)
            .map_err(|_| HolonError::PopulationReservation)?;
        self.residual_incidences
            .try_reserve_exact(additional_residuals)
            .map_err(|_| HolonError::PopulationReservation)?;
        Ok(())
    }

    fn preflight_settlement(
        &mut self,
        sources: usize,
        origins: usize,
        lineages: usize,
    ) -> Result<(), HolonError> {
        self.settlements
            .try_reserve(1)
            .map_err(|_| HolonError::PopulationReservation)?;
        self.source_dispositions
            .try_reserve_exact(sources)
            .map_err(|_| HolonError::PopulationReservation)?;
        self.return_origins
            .try_reserve_exact(origins)
            .map_err(|_| HolonError::PopulationReservation)?;
        self.lineage_incidences
            .try_reserve_exact(lineages)
            .map_err(|_| HolonError::PopulationReservation)?;
        Ok(())
    }

    /// Derive the unresolved FOUND incidence sections from the complete enacted population. The
    /// selected cut's incidence is the only boundary; no source type, score, or later usefulness
    /// predicate participates.
    fn found_incidence_offsets(
        enacted: &EnactedPopulation,
        cut: u64,
    ) -> Result<Vec<u64>, HolonError> {
        let active = enacted.active();
        let cut_span = active
            .cuts
            .get(usize::try_from(cut).map_err(|_| HolonError::CutAbsent)?)
            .copied()
            .ok_or(HolonError::CutAbsent)?;
        let incidence_extent =
            usize::try_from(cut_span.incidences()).map_err(|_| HolonError::PopulationOverflow)?;
        let mut found = Vec::new();
        found
            .try_reserve_exact(incidence_extent)
            .map_err(|_| HolonError::PopulationReservation)?;
        let journal = enacted.emissions();
        for local in 0..cut_span.incidences() {
            let global = cut_span
                .incidence_offset()
                .checked_add(local)
                .ok_or(HolonError::PopulationOverflow)?;
            let incidence = active
                .incidences
                .get(usize::try_from(global).map_err(|_| HolonError::PopulationOverflow)?)
                .copied()
                .ok_or(HolonError::CutAbsent)?;
            let current = active
                .currents
                .get(
                    usize::try_from(incidence.current())
                        .map_err(|_| HolonError::PopulationOverflow)?,
                )
                .copied()
                .ok_or(HolonError::CutAbsent)?;
            let first_event = current
                .event_offset()
                .checked_add(incidence.current_event_offset())
                .ok_or(HolonError::PopulationOverflow)?;
            let after_event = first_event
                .checked_add(incidence.current_events())
                .ok_or(HolonError::PopulationOverflow)?;
            let mut carries_found = false;
            for event in first_event..after_event {
                let span = journal
                    .events
                    .get(usize::try_from(event).map_err(|_| HolonError::PopulationOverflow)?)
                    .copied()
                    .ok_or(HolonError::CutAbsent)?;
                let after_deed = span
                    .deed_offset()
                    .checked_add(span.deeds())
                    .ok_or(HolonError::PopulationOverflow)?;
                for deed in span.deed_offset()..after_deed {
                    let kind = journal
                        .deeds
                        .get(usize::try_from(deed).map_err(|_| HolonError::PopulationOverflow)?)
                        .copied()
                        .ok_or(HolonError::CutAbsent)?
                        .kind();
                    if matches!(kind, DeedKind::FoundThis | DeedKind::FoundThat) {
                        carries_found = true;
                        break;
                    }
                }
                if carries_found {
                    break;
                }
            }
            if carries_found {
                found.push(local);
            }
        }
        Ok(found)
    }

    fn mount_unchecked(&mut self, surface: LiveSurface) -> Result<SurfaceId, HolonError> {
        let ordinal =
            u64::try_from(self.surfaces.len()).map_err(|_| HolonError::PopulationOverflow)?;
        self.surfaces.push(surface);
        Ok(SurfaceId(ordinal))
    }

    /// Retain one active surface.  No wire encoding, source material clone, or semantic registration
    /// occurs.  The returned ordinal is local to this living receiver.
    pub fn mount(&mut self, surface: Arc<ActiveCut>) -> Result<SurfaceId, HolonError> {
        surface.validate().map_err(HolonError::SurfaceInvalid)?;
        self.surfaces
            .try_reserve(1)
            .map_err(|_| HolonError::PopulationReservation)?;
        self.mount_unchecked(LiveSurface::Active(surface))
    }

    pub fn mount_standing(
        &mut self,
        surface: Arc<SparseStandingSurface>,
    ) -> Result<SurfaceId, HolonError> {
        self.surfaces
            .try_reserve(1)
            .map_err(|_| HolonError::PopulationReservation)?;
        self.mount_unchecked(LiveSurface::Standing(surface))
    }

    pub fn mount_enacted(
        &mut self,
        surface: Arc<EnactedPopulation>,
    ) -> Result<SurfaceId, HolonError> {
        surface
            .active()
            .validate()
            .map_err(HolonError::SurfaceInvalid)?;
        self.surfaces
            .try_reserve(1)
            .map_err(|_| HolonError::PopulationReservation)?;
        self.mount_unchecked(LiveSurface::Enacted(surface))
    }

    pub fn cut(&self, surface: SurfaceId, cut: u64) -> Result<CutRef, HolonError> {
        let surface_index = usize::try_from(surface.0).map_err(|_| HolonError::SurfaceAbsent)?;
        let active = self
            .surfaces
            .get(surface_index)
            .ok_or(HolonError::SurfaceAbsent)?;
        if cut >= active.cuts() {
            return Err(HolonError::CutAbsent);
        }
        Ok(CutRef(BoundaryCut::new(surface.0, cut)))
    }

    pub fn begin(&mut self, before: CutRef) -> Result<TransitionId, HolonError> {
        self.cut(before.surface(), before.cut())?;
        let before_ordinal =
            u64::try_from(self.cuts.len()).map_err(|_| HolonError::PopulationOverflow)?;
        let id = TransitionId(self.transitions.len());
        self.cuts
            .try_reserve(1)
            .map_err(|_| HolonError::PopulationReservation)?;
        self.transitions
            .try_reserve(1)
            .map_err(|_| HolonError::PopulationReservation)?;
        self.cuts.push(before.0);
        self.transitions.push(TransitionState::Open(OpenTransition {
            roles: [before_ordinal, 0, 0, 0, 0, 0],
            phase: 1,
            residual_incidence_offset: 0,
            residual_incidences: 0,
            provisional: None,
        }));
        Ok(id)
    }

    fn open_mut(&mut self, id: TransitionId) -> Result<&mut OpenTransition, HolonError> {
        match self.transitions.get_mut(id.0) {
            Some(TransitionState::Open(open)) => Ok(open),
            Some(TransitionState::Closed { .. } | TransitionState::SettledSilent { .. }) => {
                Err(HolonError::TransitionClosed)
            }
            None => Err(HolonError::TransitionAbsent),
        }
    }

    fn append_role(
        &mut self,
        id: TransitionId,
        expected_phase: u8,
        cut: CutRef,
    ) -> Result<(), HolonError> {
        let actual = match self.transitions.get(id.0) {
            Some(TransitionState::Open(open)) => open.phase,
            Some(TransitionState::Closed { .. } | TransitionState::SettledSilent { .. }) => {
                return Err(HolonError::TransitionClosed)
            }
            None => return Err(HolonError::TransitionAbsent),
        };
        if actual != expected_phase {
            return Err(HolonError::WrongPhase {
                expected: expected_phase,
                actual,
            });
        }
        self.cut(cut.surface(), cut.cut())?;
        let existing_cut = self.cuts.iter().position(|row| *row == cut.0);
        let cut_ordinal = match existing_cut {
            Some(ordinal) => u64::try_from(ordinal).map_err(|_| HolonError::PopulationOverflow)?,
            None => u64::try_from(self.cuts.len()).map_err(|_| HolonError::PopulationOverflow)?,
        };
        if existing_cut.is_none() {
            self.cuts
                .try_reserve(1)
                .map_err(|_| HolonError::PopulationReservation)?;
        }
        if existing_cut.is_none() {
            self.cuts.push(cut.0);
        }
        let open = self.open_mut(id)?;
        open.roles[expected_phase as usize] = cut_ordinal;
        open.phase += 1;
        Ok(())
    }

    pub fn meeting(&mut self, id: TransitionId, cut: CutRef) -> Result<(), HolonError> {
        self.append_role(id, 1, cut)
    }

    pub fn deed(&mut self, id: TransitionId, cut: CutRef) -> Result<(), HolonError> {
        self.append_role(id, 2, cut)
    }

    pub fn consequence(&mut self, id: TransitionId, cut: CutRef) -> Result<(), HolonError> {
        self.append_role(id, 3, cut)
    }

    pub fn returned(&mut self, id: TransitionId, cut: CutRef) -> Result<(), HolonError> {
        self.append_role(id, 4, cut)
    }

    /// Retain one exact nonempty incidence section as unresolved.  It names active cut incidence,
    /// not a copied event or observer description.
    pub fn retain_residual(
        &mut self,
        id: TransitionId,
        cut: CutRef,
        incidence_offset: u64,
        incidences: u64,
    ) -> Result<(), HolonError> {
        let phase = match self.transitions.get(id.0) {
            Some(TransitionState::Open(open)) => open.phase,
            Some(TransitionState::Closed { .. } | TransitionState::SettledSilent { .. }) => {
                return Err(HolonError::TransitionClosed)
            }
            None => return Err(HolonError::TransitionAbsent),
        };
        if phase == 0 || phase >= 6 {
            return Err(HolonError::TransitionClosed);
        }
        let surface_index =
            usize::try_from(cut.surface().0).map_err(|_| HolonError::SurfaceAbsent)?;
        let cut_index = usize::try_from(cut.cut()).map_err(|_| HolonError::CutAbsent)?;
        let active = self
            .surfaces
            .get(surface_index)
            .ok_or(HolonError::SurfaceAbsent)?;
        let cut_incidences = active.incidences(cut_index).ok_or(HolonError::CutAbsent)?;
        let end = incidence_offset
            .checked_add(incidences)
            .ok_or(HolonError::ResidualAbsent)?;
        if incidences == 0 || end > cut_incidences {
            return Err(HolonError::ResidualAbsent);
        }

        let existing_cut = self.cuts.iter().position(|row| *row == cut.0);
        let cut_ordinal = match existing_cut {
            Some(ordinal) => u64::try_from(ordinal).map_err(|_| HolonError::PopulationOverflow)?,
            None => u64::try_from(self.cuts.len()).map_err(|_| HolonError::PopulationOverflow)?,
        };
        let residual = ResidualSpan::new(cut_ordinal, incidence_offset, incidences)
            .ok_or(HolonError::ResidualAbsent)?;
        let residual_ordinal =
            u64::try_from(self.residuals.len()).map_err(|_| HolonError::PopulationOverflow)?;
        let incidence_ordinal = u64::try_from(self.residual_incidences.len())
            .map_err(|_| HolonError::PopulationOverflow)?;

        let open = match self.transitions.get(id.0) {
            Some(TransitionState::Open(open)) => open,
            Some(TransitionState::Closed { .. } | TransitionState::SettledSilent { .. }) => {
                return Err(HolonError::TransitionClosed)
            }
            None => return Err(HolonError::TransitionAbsent),
        };
        if open.residual_incidences != 0
            && open
                .residual_incidence_offset
                .checked_add(open.residual_incidences)
                != Some(incidence_ordinal)
        {
            return Err(HolonError::PopulationOverflow);
        }
        let next_residuals = open
            .residual_incidences
            .checked_add(1)
            .ok_or(HolonError::PopulationOverflow)?;

        if existing_cut.is_none() {
            self.cuts
                .try_reserve(1)
                .map_err(|_| HolonError::PopulationReservation)?;
        }
        self.residuals
            .try_reserve(1)
            .map_err(|_| HolonError::PopulationReservation)?;
        self.residual_incidences
            .try_reserve(1)
            .map_err(|_| HolonError::PopulationReservation)?;
        if existing_cut.is_none() {
            self.cuts.push(cut.0);
        }
        self.residuals.push(residual);
        self.residual_incidences
            .push(ResidualIncidence::new(residual_ordinal));
        let open = self.open_mut(id)?;
        if open.residual_incidences == 0 {
            open.residual_incidence_offset = incidence_ordinal;
        }
        open.residual_incidences = next_residuals;
        Ok(())
    }

    /// Append the actual after-cut and close the receipt.  No earlier role can be absent because
    /// every phase transition above is ordered and a closed receipt is built only here.
    #[cfg(test)]
    pub fn after(
        &mut self,
        id: TransitionId,
        cut: CutRef,
    ) -> Result<TransitionReceipt, HolonError> {
        self.cut(cut.surface(), cut.cut())?;
        let mut open = match self.transitions.get(id.0) {
            Some(TransitionState::Open(open)) if open.phase == 5 => open.clone(),
            Some(TransitionState::Open(open)) => {
                return Err(HolonError::WrongPhase {
                    expected: 5,
                    actual: open.phase,
                })
            }
            Some(TransitionState::Closed { .. } | TransitionState::SettledSilent { .. }) => {
                return Err(HolonError::TransitionClosed)
            }
            None => return Err(HolonError::TransitionAbsent),
        };
        let cut_ordinal =
            u64::try_from(self.cuts.len()).map_err(|_| HolonError::PopulationOverflow)?;
        open.roles[5] = cut_ordinal;
        open.phase = 6;
        let (residual_offset, residuals) = if open.residual_incidences == 0 {
            (0, 0)
        } else {
            (open.residual_incidence_offset, open.residual_incidences)
        };
        let receipt = TransitionReceipt::new(
            open.roles[0],
            open.roles[1],
            open.roles[2],
            open.roles[3],
            open.roles[4],
            open.roles[5],
            residual_offset,
            residuals,
        )
        .ok_or(HolonError::PopulationOverflow)?;
        let ordinal =
            u64::try_from(self.receipts.len()).map_err(|_| HolonError::PopulationOverflow)?;
        self.cuts
            .try_reserve(1)
            .map_err(|_| HolonError::PopulationReservation)?;
        self.receipts
            .try_reserve(1)
            .map_err(|_| HolonError::PopulationReservation)?;
        self.cuts.push(cut.0);
        self.receipts.push(receipt);
        self.transitions[id.0] = TransitionState::Closed {
            receipt: ordinal,
            settlement: None,
        };
        Ok(receipt)
    }

    /// Atomically install the three roles which have genuinely lived before the world interval:
    /// receiver-before, presented meeting, and the complete enacted deed population.  All
    /// validation and allocation boundaries close before the first live row is appended.
    pub(crate) fn open_enacted(
        &mut self,
        before: Arc<SparseStandingSurface>,
        enacted: Arc<EnactedPopulation>,
        cut: u64,
    ) -> Result<TransitionId, HolonError> {
        if cut >= enacted.active().header.cuts() || enacted.prepared_cut(cut).is_none() {
            return Err(HolonError::CutAbsent);
        }
        let found_incidences = Self::found_incidence_offsets(&enacted, cut)?;
        let first_cut =
            u64::try_from(self.cuts.len()).map_err(|_| HolonError::PopulationOverflow)?;
        let second_cut = first_cut
            .checked_add(1)
            .ok_or(HolonError::PopulationOverflow)?;
        let third_cut = first_cut
            .checked_add(2)
            .ok_or(HolonError::PopulationOverflow)?;
        let transition = TransitionId(self.transitions.len());
        self.preflight_populations(3, 3, 1, 1, 0, found_incidences.len())?;

        let before_surface = self.mount_unchecked(LiveSurface::Standing(before))?;
        let meeting_surface =
            self.mount_unchecked(LiveSurface::Active(enacted.active().clone()))?;
        let deed_surface = self.mount_unchecked(LiveSurface::Enacted(enacted))?;
        self.cuts.push(BoundaryCut::new(before_surface.0, 0));
        self.cuts.push(BoundaryCut::new(meeting_surface.0, cut));
        self.cuts.push(BoundaryCut::new(deed_surface.0, cut));
        let residual_incidence_offset = u64::try_from(self.residual_incidences.len())
            .map_err(|_| HolonError::PopulationOverflow)?;
        for local in &found_incidences {
            let residual_ordinal =
                u64::try_from(self.residuals.len()).map_err(|_| HolonError::PopulationOverflow)?;
            self.residuals.push(
                ResidualSpan::new(third_cut, *local, 1).ok_or(HolonError::PopulationOverflow)?,
            );
            self.residual_incidences
                .push(ResidualIncidence::new(residual_ordinal));
        }
        self.transitions.push(TransitionState::Open(OpenTransition {
            roles: [first_cut, second_cut, third_cut, 0, 0, 0],
            phase: 3,
            residual_incidence_offset: if found_incidences.is_empty() {
                0
            } else {
                residual_incidence_offset
            },
            residual_incidences: u64::try_from(found_incidences.len())
                .map_err(|_| HolonError::PopulationOverflow)?,
            provisional: None,
        }));
        Ok(transition)
    }

    /// Commit the world consequence before return conduct. Repeating the exact role on the same
    /// transition is idempotent; a different surface or cut refuses.
    pub(crate) fn commit_consequence(
        &mut self,
        id: TransitionId,
        consequence: Arc<ActiveCut>,
        consequence_cut: u64,
    ) -> Result<(), HolonError> {
        consequence.validate().map_err(HolonError::SurfaceInvalid)?;
        if consequence_cut >= consequence.header.cuts() {
            return Err(HolonError::CutAbsent);
        }
        let phase = match self.transitions.get(id.0) {
            Some(TransitionState::Open(open)) => open.phase,
            Some(TransitionState::Closed { .. } | TransitionState::SettledSilent { .. }) => {
                return Err(HolonError::TransitionClosed)
            }
            None => return Err(HolonError::TransitionAbsent),
        };
        if phase >= 4 {
            let open = match &self.transitions[id.0] {
                TransitionState::Open(open) => open,
                _ => unreachable!(),
            };
            let mounted_cut = self
                .cuts
                .get(usize::try_from(open.roles[3]).map_err(|_| HolonError::CutAbsent)?)
                .copied()
                .ok_or(HolonError::CutAbsent)?;
            let mounted = self
                .surfaces
                .get(usize::try_from(mounted_cut.body()).map_err(|_| HolonError::SurfaceAbsent)?)
                .and_then(LiveSurface::active)
                .ok_or(HolonError::SurfaceAbsent)?;
            return if mounted_cut.cut() == consequence_cut && **mounted == *consequence {
                Ok(())
            } else {
                Err(HolonError::RecoveryInvalid)
            };
        }
        if phase != 3 {
            return Err(HolonError::WrongPhase {
                expected: 3,
                actual: phase,
            });
        }
        self.preflight_populations(1, 1, 0, 0, 0, 0)?;
        let surface = self.mount_unchecked(LiveSurface::Active(consequence))?;
        let ordinal = u64::try_from(self.cuts.len()).map_err(|_| HolonError::PopulationOverflow)?;
        self.cuts.push(BoundaryCut::new(surface.0, consequence_cut));
        let open = self.open_mut(id)?;
        open.roles[3] = ordinal;
        open.phase = 4;
        Ok(())
    }

    /// Commit the already-conducted return and its exact settlement populations. Allocation for
    /// the final after-role and receipt is reserved here, before phase five becomes visible.
    pub(crate) fn commit_returned(
        &mut self,
        id: TransitionId,
        returned: Arc<EnactedPopulation>,
        return_cut: u64,
        sources: &[SourceDispositionRow],
        origins: &[ReturnOriginRow],
        lineages: &[LineageIncidenceRow],
    ) -> Result<(), HolonError> {
        match self.transitions.get(id.0) {
            Some(TransitionState::Open(open)) if open.phase == 4 => {}
            Some(TransitionState::Open(open)) if open.phase == 5 => {
                let cut = self
                    .cuts
                    .get(usize::try_from(open.roles[4]).map_err(|_| HolonError::CutAbsent)?)
                    .copied()
                    .ok_or(HolonError::CutAbsent)?;
                let mounted = self
                    .surfaces
                    .get(usize::try_from(cut.body()).map_err(|_| HolonError::SurfaceAbsent)?)
                    .and_then(LiveSurface::enacted)
                    .ok_or(HolonError::SurfaceAbsent)?;
                let provisional = open.provisional.ok_or(HolonError::RecoveryInvalid)?;
                let source_first = usize::try_from(provisional.source_offset)
                    .map_err(|_| HolonError::RecoveryInvalid)?;
                let source_after = usize::try_from(
                    provisional
                        .source_offset
                        .checked_add(provisional.sources)
                        .ok_or(HolonError::RecoveryInvalid)?,
                )
                .map_err(|_| HolonError::RecoveryInvalid)?;
                let origin_first = usize::try_from(provisional.origin_offset)
                    .map_err(|_| HolonError::RecoveryInvalid)?;
                let origin_after = usize::try_from(
                    provisional
                        .origin_offset
                        .checked_add(provisional.origins)
                        .ok_or(HolonError::RecoveryInvalid)?,
                )
                .map_err(|_| HolonError::RecoveryInvalid)?;
                let lineage_first = usize::try_from(provisional.lineage_offset)
                    .map_err(|_| HolonError::RecoveryInvalid)?;
                let lineage_after = usize::try_from(
                    provisional
                        .lineage_offset
                        .checked_add(provisional.lineages)
                        .ok_or(HolonError::RecoveryInvalid)?,
                )
                .map_err(|_| HolonError::RecoveryInvalid)?;
                return if Arc::ptr_eq(mounted, &returned)
                    && cut.cut() == return_cut
                    && self.source_dispositions.get(source_first..source_after) == Some(sources)
                    && self.return_origins.get(origin_first..origin_after) == Some(origins)
                    && self.lineage_incidences.get(lineage_first..lineage_after) == Some(lineages)
                {
                    Ok(())
                } else {
                    Err(HolonError::RecoveryInvalid)
                };
            }
            Some(TransitionState::Open(open)) => {
                return Err(HolonError::WrongPhase {
                    expected: 4,
                    actual: open.phase,
                })
            }
            Some(TransitionState::Closed { .. } | TransitionState::SettledSilent { .. }) => {
                return Err(HolonError::TransitionClosed)
            }
            None => return Err(HolonError::TransitionAbsent),
        }
        if return_cut >= returned.active().header.cuts()
            || returned.prepared_cut(return_cut).is_none()
            || sources.is_empty()
        {
            return Err(HolonError::CutAbsent);
        }
        let source_offset = u64::try_from(self.source_dispositions.len())
            .map_err(|_| HolonError::PopulationOverflow)?;
        let origin_offset = if origins.is_empty() {
            0
        } else {
            u64::try_from(self.return_origins.len()).map_err(|_| HolonError::PopulationOverflow)?
        };
        let lineage_offset = if lineages.is_empty() {
            0
        } else {
            u64::try_from(self.lineage_incidences.len())
                .map_err(|_| HolonError::PopulationOverflow)?
        };
        let provisional = ProvisionalSettlement {
            source_offset,
            sources: u64::try_from(sources.len()).map_err(|_| HolonError::PopulationOverflow)?,
            origin_offset,
            origins: u64::try_from(origins.len()).map_err(|_| HolonError::PopulationOverflow)?,
            lineage_offset,
            lineages: u64::try_from(lineages.len()).map_err(|_| HolonError::PopulationOverflow)?,
        };
        // Return now; after surface, cut, receipt, and settlement later. The latter capacity is
        // reserved here so an uninterrupted phase-five close has no allocation boundary.
        self.preflight_populations(2, 2, 0, 1, 0, 0)?;
        self.preflight_settlement(sources.len(), origins.len(), lineages.len())?;
        let return_surface = self.mount_unchecked(LiveSurface::Enacted(returned))?;
        let return_ordinal =
            u64::try_from(self.cuts.len()).map_err(|_| HolonError::PopulationOverflow)?;
        self.cuts
            .push(BoundaryCut::new(return_surface.0, return_cut));
        self.source_dispositions.extend_from_slice(sources);
        self.return_origins.extend_from_slice(origins);
        self.lineage_incidences.extend_from_slice(lineages);
        let open = self.open_mut(id)?;
        open.roles[4] = return_ordinal;
        open.phase = 5;
        open.provisional = Some(provisional);
        Ok(())
    }

    /// Install the successor body and close a phase-five return. Recovery can call this directly;
    /// source conduct, world action, and return conduct are not repeated.
    pub(crate) fn finish_returned(
        &mut self,
        id: TransitionId,
        after: Arc<SparseStandingSurface>,
    ) -> Result<TransitionReceipt, HolonError> {
        let open = match self.transitions.get(id.0) {
            Some(TransitionState::Open(open)) if open.phase == 5 => open.clone(),
            Some(TransitionState::Open(open)) => {
                return Err(HolonError::WrongPhase {
                    expected: 5,
                    actual: open.phase,
                })
            }
            Some(TransitionState::Closed { .. } | TransitionState::SettledSilent { .. }) => {
                return Err(HolonError::TransitionClosed)
            }
            None => return Err(HolonError::TransitionAbsent),
        };
        let provisional = open.provisional.ok_or(HolonError::RecoveryInvalid)?;
        let after_ordinal =
            u64::try_from(self.cuts.len()).map_err(|_| HolonError::PopulationOverflow)?;
        let residual = if open.residual_incidences == 0 {
            (0, 0)
        } else {
            (open.residual_incidence_offset, open.residual_incidences)
        };
        let receipt = TransitionReceipt::new(
            open.roles[0],
            open.roles[1],
            open.roles[2],
            open.roles[3],
            open.roles[4],
            after_ordinal,
            residual.0,
            residual.1,
        )
        .ok_or(HolonError::PopulationOverflow)?;
        let receipt_ordinal =
            u64::try_from(self.receipts.len()).map_err(|_| HolonError::PopulationOverflow)?;
        let settlement_ordinal =
            u64::try_from(self.settlements.len()).map_err(|_| HolonError::PopulationOverflow)?;
        let settlement = SettlementSpan::returned(
            u64::try_from(id.0).map_err(|_| HolonError::PopulationOverflow)?,
            receipt_ordinal,
            provisional.source_offset,
            provisional.sources,
            provisional.origin_offset,
            provisional.origins,
            provisional.lineage_offset,
            provisional.lineages,
        )
        .ok_or(HolonError::PopulationOverflow)?;
        // A recovered phase-five image does not retain Vec capacity, so close its only remaining
        // allocation boundary before appending the after role.
        self.preflight_populations(1, 1, 0, 1, 0, 0)?;
        self.settlements
            .try_reserve(1)
            .map_err(|_| HolonError::PopulationReservation)?;
        let after_surface = self.mount_unchecked(LiveSurface::Standing(after))?;
        self.cuts.push(BoundaryCut::new(after_surface.0, 0));
        self.receipts.push(receipt);
        self.settlements.push(settlement);
        self.transitions[id.0] = TransitionState::Closed {
            receipt: receipt_ordinal,
            settlement: Some(settlement_ordinal),
        };
        Ok(receipt)
    }

    /// Close a source contact which resolved to exact silence. The source meeting and deed have
    /// already changed the receiver, so their post-deed standing surface is a genuinely lived
    /// after role. No world consequence or return surface is manufactured to fill the six-role
    /// shape.
    pub(crate) fn settle_silent(
        &mut self,
        id: TransitionId,
        after: Arc<SparseStandingSurface>,
        sources: &[SourceDispositionRow],
    ) -> Result<SilentReceipt, HolonError> {
        let open = match self.transitions.get(id.0) {
            Some(TransitionState::Open(open)) if open.phase == 3 => open.clone(),
            Some(TransitionState::Open(open)) => {
                return Err(HolonError::WrongPhase {
                    expected: 3,
                    actual: open.phase,
                })
            }
            Some(TransitionState::Closed { .. } | TransitionState::SettledSilent { .. }) => {
                return Err(HolonError::TransitionClosed)
            }
            None => return Err(HolonError::TransitionAbsent),
        };
        let after_ordinal =
            u64::try_from(self.cuts.len()).map_err(|_| HolonError::PopulationOverflow)?;
        let residual = if open.residual_incidences == 0 {
            (0, 0)
        } else {
            (open.residual_incidence_offset, open.residual_incidences)
        };
        let receipt = SilentReceipt::new(
            open.roles[0],
            open.roles[1],
            open.roles[2],
            after_ordinal,
            residual.0,
            residual.1,
        )
        .ok_or(HolonError::PopulationOverflow)?;
        let receipt_ordinal = u64::try_from(self.silent_receipts.len())
            .map_err(|_| HolonError::PopulationOverflow)?;
        let settlement_ordinal =
            u64::try_from(self.settlements.len()).map_err(|_| HolonError::PopulationOverflow)?;
        let source_offset = u64::try_from(self.source_dispositions.len())
            .map_err(|_| HolonError::PopulationOverflow)?;
        let settlement = SettlementSpan::silent(
            u64::try_from(id.0).map_err(|_| HolonError::PopulationOverflow)?,
            receipt_ordinal,
            source_offset,
            u64::try_from(sources.len()).map_err(|_| HolonError::PopulationOverflow)?,
        )
        .ok_or(HolonError::PopulationOverflow)?;
        self.preflight_populations(1, 1, 0, 0, 1, 0)?;
        self.preflight_settlement(sources.len(), 0, 0)?;

        let after_surface = self.mount_unchecked(LiveSurface::Standing(after))?;
        self.cuts.push(BoundaryCut::new(after_surface.0, 0));
        self.silent_receipts.push(receipt);
        self.source_dispositions.extend_from_slice(sources);
        self.settlements.push(settlement);
        self.transitions[id.0] = TransitionState::SettledSilent {
            receipt: receipt_ordinal,
            settlement: settlement_ordinal,
        };
        Ok(receipt)
    }

    /// Verify that an open capability names the exact enacted owner mounted in this Holon.  Local
    /// transition ordinals are insufficient across ecologies; Arc identity is the live ownership
    /// relation and does not depend on source provenance or content.
    pub(crate) fn open_enacted_is(
        &self,
        id: TransitionId,
        enacted: &Arc<EnactedPopulation>,
    ) -> Result<bool, HolonError> {
        let open = match self.transitions.get(id.0) {
            Some(TransitionState::Open(open)) if (3..=5).contains(&open.phase) => open,
            Some(TransitionState::Open(open)) => {
                return Err(HolonError::WrongPhase {
                    expected: 3,
                    actual: open.phase,
                })
            }
            Some(TransitionState::Closed { .. } | TransitionState::SettledSilent { .. }) => {
                return Err(HolonError::TransitionClosed)
            }
            None => return Err(HolonError::TransitionAbsent),
        };
        let deed_cut = self
            .cuts
            .get(usize::try_from(open.roles[2]).map_err(|_| HolonError::CutAbsent)?)
            .ok_or(HolonError::CutAbsent)?;
        let surface = self
            .surfaces
            .get(usize::try_from(deed_cut.body()).map_err(|_| HolonError::SurfaceAbsent)?)
            .ok_or(HolonError::SurfaceAbsent)?;
        Ok(surface
            .enacted()
            .is_some_and(|mounted| Arc::ptr_eq(mounted, enacted)))
    }

    pub(crate) fn open_deed(
        &self,
        id: TransitionId,
    ) -> Result<(Arc<EnactedPopulation>, u64), HolonError> {
        let open = match self.transitions.get(id.0) {
            Some(TransitionState::Open(open)) if (3..=5).contains(&open.phase) => open,
            Some(TransitionState::Open(open)) => {
                return Err(HolonError::WrongPhase {
                    expected: 3,
                    actual: open.phase,
                })
            }
            Some(TransitionState::Closed { .. } | TransitionState::SettledSilent { .. }) => {
                return Err(HolonError::TransitionClosed)
            }
            None => return Err(HolonError::TransitionAbsent),
        };
        let deed_cut = self
            .cuts
            .get(usize::try_from(open.roles[2]).map_err(|_| HolonError::CutAbsent)?)
            .copied()
            .ok_or(HolonError::CutAbsent)?;
        let enacted = self
            .surfaces
            .get(usize::try_from(deed_cut.body()).map_err(|_| HolonError::SurfaceAbsent)?)
            .and_then(LiveSurface::enacted)
            .cloned()
            .ok_or(HolonError::SurfaceAbsent)?;
        Ok((enacted, deed_cut.cut()))
    }

    pub(crate) fn phase_five_surfaces(
        &self,
        id: TransitionId,
    ) -> Result<(Arc<EnactedPopulation>, u64, Arc<EnactedPopulation>, u64), HolonError> {
        let open = match self.transitions.get(id.0) {
            Some(TransitionState::Open(open)) if open.phase == 5 => open,
            Some(TransitionState::Open(open)) => {
                return Err(HolonError::WrongPhase {
                    expected: 5,
                    actual: open.phase,
                })
            }
            Some(TransitionState::Closed { .. } | TransitionState::SettledSilent { .. }) => {
                return Err(HolonError::TransitionClosed)
            }
            None => return Err(HolonError::TransitionAbsent),
        };
        let resolve = |role: u64| -> Result<(Arc<EnactedPopulation>, u64), HolonError> {
            let cut = self
                .cuts
                .get(usize::try_from(role).map_err(|_| HolonError::CutAbsent)?)
                .copied()
                .ok_or(HolonError::CutAbsent)?;
            let enacted = self
                .surfaces
                .get(usize::try_from(cut.body()).map_err(|_| HolonError::SurfaceAbsent)?)
                .and_then(LiveSurface::enacted)
                .cloned()
                .ok_or(HolonError::SurfaceAbsent)?;
            Ok((enacted, cut.cut()))
        };
        let (source, source_cut) = resolve(open.roles[2])?;
        let (returned, return_cut) = resolve(open.roles[4])?;
        Ok((source, source_cut, returned, return_cut))
    }

    pub fn phase(&self, id: TransitionId) -> Result<u8, HolonError> {
        match self.transitions.get(id.0) {
            Some(TransitionState::Open(open)) => Ok(open.phase),
            Some(TransitionState::Closed { .. } | TransitionState::SettledSilent { .. }) => {
                Err(HolonError::TransitionClosed)
            }
            None => Err(HolonError::TransitionAbsent),
        }
    }

    pub fn transition_status(&self, id: TransitionId) -> Result<TransitionStatus, HolonError> {
        match self.transitions.get(id.0) {
            Some(TransitionState::Open(open)) => Ok(TransitionStatus::Open(open.phase)),
            Some(TransitionState::Closed { .. }) => Ok(TransitionStatus::Returned),
            Some(TransitionState::SettledSilent { .. }) => Ok(TransitionStatus::Silent),
            None => Err(HolonError::TransitionAbsent),
        }
    }

    /// Resolve one already-lived six-role boundary. Role ordinals are the canonical
    /// before/meeting/deed/consequence/return/after order; silent intervals expose only
    /// before/meeting/deed/after.
    pub fn transition_role_cut(&self, id: TransitionId, role: u8) -> Result<CutRef, HolonError> {
        let ordinal = match self.transitions.get(id.0) {
            Some(TransitionState::Open(open)) => {
                if role >= open.phase {
                    return Err(HolonError::WrongPhase {
                        expected: role.saturating_add(1),
                        actual: open.phase,
                    });
                }
                open.roles[usize::from(role)]
            }
            Some(TransitionState::Closed { receipt, .. }) => {
                let receipt = *self
                    .receipts
                    .get(usize::try_from(*receipt).map_err(|_| HolonError::PopulationOverflow)?)
                    .ok_or(HolonError::TransitionAbsent)?;
                match role {
                    0 => receipt.before_cut(),
                    1 => receipt.meeting_cut(),
                    2 => receipt.deed_cut(),
                    3 => receipt.consequence_cut(),
                    4 => receipt.return_cut(),
                    5 => receipt.after_cut(),
                    _ => return Err(HolonError::CutAbsent),
                }
            }
            Some(TransitionState::SettledSilent { receipt, .. }) => {
                let receipt = *self
                    .silent_receipts
                    .get(usize::try_from(*receipt).map_err(|_| HolonError::PopulationOverflow)?)
                    .ok_or(HolonError::TransitionAbsent)?;
                match role {
                    0 => receipt.before_cut(),
                    1 => receipt.meeting_cut(),
                    2 => receipt.deed_cut(),
                    5 => receipt.after_cut(),
                    _ => return Err(HolonError::CutAbsent),
                }
            }
            None => return Err(HolonError::TransitionAbsent),
        };
        self.boundary_cut(ordinal)
    }

    pub fn surface(&self, id: SurfaceId) -> Result<&LiveSurface, HolonError> {
        self.surfaces
            .get(usize::try_from(id.0).map_err(|_| HolonError::SurfaceAbsent)?)
            .ok_or(HolonError::SurfaceAbsent)
    }

    pub fn boundary_cut(&self, ordinal: u64) -> Result<CutRef, HolonError> {
        self.cuts
            .get(usize::try_from(ordinal).map_err(|_| HolonError::CutAbsent)?)
            .copied()
            .map(CutRef)
            .ok_or(HolonError::CutAbsent)
    }

    pub fn receipt(&self, id: TransitionId) -> Result<TransitionReceipt, HolonError> {
        match self.transitions.get(id.0) {
            Some(TransitionState::Closed { receipt, .. }) => self
                .receipts
                .get(usize::try_from(*receipt).map_err(|_| HolonError::PopulationOverflow)?)
                .copied()
                .ok_or(HolonError::TransitionAbsent),
            Some(TransitionState::SettledSilent { .. }) => Err(HolonError::TransitionClosed),
            Some(TransitionState::Open(_)) => Err(HolonError::WrongPhase {
                expected: 6,
                actual: self.phase(id)?,
            }),
            None => Err(HolonError::TransitionAbsent),
        }
    }

    pub fn silent_receipt(&self, id: TransitionId) -> Result<SilentReceipt, HolonError> {
        match self.transitions.get(id.0) {
            Some(TransitionState::SettledSilent { receipt, .. }) => self
                .silent_receipts
                .get(usize::try_from(*receipt).map_err(|_| HolonError::PopulationOverflow)?)
                .copied()
                .ok_or(HolonError::TransitionAbsent),
            Some(TransitionState::Closed { .. }) => Err(HolonError::TransitionClosed),
            Some(TransitionState::Open(_)) => Err(HolonError::WrongPhase {
                expected: 4,
                actual: self.phase(id)?,
            }),
            None => Err(HolonError::TransitionAbsent),
        }
    }

    pub fn settlement_header(&self) -> Result<SettlementHeader, HolonError> {
        SettlementHeader::new(
            u64::try_from(self.settlements.len()).map_err(|_| HolonError::PopulationOverflow)?,
            u64::try_from(self.silent_receipts.len())
                .map_err(|_| HolonError::PopulationOverflow)?,
            u64::try_from(self.source_dispositions.len())
                .map_err(|_| HolonError::PopulationOverflow)?,
            u64::try_from(self.return_origins.len()).map_err(|_| HolonError::PopulationOverflow)?,
            u64::try_from(self.lineage_incidences.len())
                .map_err(|_| HolonError::PopulationOverflow)?,
        )
        .ok_or(HolonError::PopulationOverflow)
    }

    pub fn settlement(&self, id: TransitionId) -> Result<SettlementView<'_>, HolonError> {
        let ordinal = match self.transitions.get(id.0) {
            Some(TransitionState::Closed {
                settlement: Some(settlement),
                ..
            })
            | Some(TransitionState::SettledSilent { settlement, .. }) => *settlement,
            Some(TransitionState::Closed {
                settlement: None, ..
            }) => return Err(HolonError::SettlementAbsent),
            Some(TransitionState::Open(_)) => return Err(HolonError::LiveInterval),
            None => return Err(HolonError::TransitionAbsent),
        };
        self.settlement_at(ordinal)
    }

    /// Exact settlement companion populations at either committed-return phase five or terminal
    /// closure. This lets recovery validate an in-flight return without manufacturing a closed
    /// settlement span early.
    pub fn settlement_populations(
        &self,
        id: TransitionId,
    ) -> Result<
        (
            &[SourceDispositionRow],
            &[ReturnOriginRow],
            &[LineageIncidenceRow],
        ),
        HolonError,
    > {
        if let Some(TransitionState::Open(open)) = self.transitions.get(id.0) {
            if open.phase != 5 {
                return Err(HolonError::WrongPhase {
                    expected: 5,
                    actual: open.phase,
                });
            }
            let provisional = open.provisional.ok_or(HolonError::RecoveryInvalid)?;
            let slice =
                |offset: u64, extent: u64, len: usize| -> Result<(usize, usize), HolonError> {
                    let first =
                        usize::try_from(offset).map_err(|_| HolonError::PopulationOverflow)?;
                    let after = usize::try_from(
                        offset
                            .checked_add(extent)
                            .ok_or(HolonError::PopulationOverflow)?,
                    )
                    .map_err(|_| HolonError::PopulationOverflow)?;
                    if after > len {
                        return Err(HolonError::RecoveryInvalid);
                    }
                    Ok((first, after))
                };
            let (source_first, source_after) = slice(
                provisional.source_offset,
                provisional.sources,
                self.source_dispositions.len(),
            )?;
            let (origin_first, origin_after) = slice(
                provisional.origin_offset,
                provisional.origins,
                self.return_origins.len(),
            )?;
            let (lineage_first, lineage_after) = slice(
                provisional.lineage_offset,
                provisional.lineages,
                self.lineage_incidences.len(),
            )?;
            return Ok((
                &self.source_dispositions[source_first..source_after],
                &self.return_origins[origin_first..origin_after],
                &self.lineage_incidences[lineage_first..lineage_after],
            ));
        }
        let settlement = self.settlement(id)?;
        Ok((
            settlement.sources(),
            settlement.origins(),
            settlement.lineages(),
        ))
    }

    /// Enumerate the settlement companion population in append order.  The ordinal is a durable
    /// population coordinate, unlike `TransitionId`, which is a live capability used to close one
    /// interval.  This makes every row counted by [`Self::settlement_header`] actually readable by
    /// recovery and substrate mirrors without reconstructing a transition lookup table.
    pub fn settlement_at(&self, ordinal: u64) -> Result<SettlementView<'_>, HolonError> {
        let span = self
            .settlements
            .get(usize::try_from(ordinal).map_err(|_| HolonError::PopulationOverflow)?)
            .copied()
            .ok_or(HolonError::SettlementAbsent)?;
        let first =
            usize::try_from(span.source_offset()).map_err(|_| HolonError::PopulationOverflow)?;
        let after = usize::try_from(
            span.source_offset()
                .checked_add(span.sources())
                .ok_or(HolonError::PopulationOverflow)?,
        )
        .map_err(|_| HolonError::PopulationOverflow)?;
        let sources = self
            .source_dispositions
            .get(first..after)
            .ok_or(HolonError::SettlementAbsent)?;
        let origins = if span.origins() == 0 {
            &[]
        } else {
            let first = usize::try_from(span.origin_offset())
                .map_err(|_| HolonError::PopulationOverflow)?;
            let after = usize::try_from(
                span.origin_offset()
                    .checked_add(span.origins())
                    .ok_or(HolonError::PopulationOverflow)?,
            )
            .map_err(|_| HolonError::PopulationOverflow)?;
            self.return_origins
                .get(first..after)
                .ok_or(HolonError::SettlementAbsent)?
        };
        let lineages = if span.lineages() == 0 {
            &[]
        } else {
            let first = usize::try_from(span.lineage_offset())
                .map_err(|_| HolonError::PopulationOverflow)?;
            let after = usize::try_from(
                span.lineage_offset()
                    .checked_add(span.lineages())
                    .ok_or(HolonError::PopulationOverflow)?,
            )
            .map_err(|_| HolonError::PopulationOverflow)?;
            self.lineage_incidences
                .get(first..after)
                .ok_or(HolonError::SettlementAbsent)?
        };
        Ok(SettlementView {
            span,
            sources,
            origins,
            lineages,
        })
    }

    /// Resolve one receipt-local residual incidence to its exact section and deed cut.
    pub fn residual(
        &self,
        receipt: TransitionReceipt,
        local: u64,
    ) -> Result<(ResidualSpan, CutRef), HolonError> {
        if local >= receipt.residual_incidences() {
            return Err(HolonError::ResidualAbsent);
        }
        let incidence = receipt
            .residual_incidence_offset()
            .checked_add(local)
            .ok_or(HolonError::PopulationOverflow)?;
        let residual_ref = self
            .residual_incidences
            .get(usize::try_from(incidence).map_err(|_| HolonError::PopulationOverflow)?)
            .copied()
            .ok_or(HolonError::ResidualAbsent)?;
        let residual = self
            .residuals
            .get(
                usize::try_from(residual_ref.ordinal())
                    .map_err(|_| HolonError::PopulationOverflow)?,
            )
            .copied()
            .ok_or(HolonError::ResidualAbsent)?;
        let cut = self.boundary_cut(residual.cut())?;
        Ok((residual, cut))
    }

    /// Capture every live row and every surface occurrence. Enacted surfaces are represented by
    /// their canonical ecology enactment ordinal so recovery can restore pointer identity without
    /// identifying equal-valued occurrences.
    pub(crate) fn checkpoint_image(
        &self,
        enacted: &[Arc<EnactedPopulation>],
    ) -> Result<LiveHolonImage, HolonError> {
        let mut surfaces = Vec::new();
        surfaces
            .try_reserve_exact(self.surfaces.len())
            .map_err(|_| HolonError::PopulationReservation)?;
        for surface in &self.surfaces {
            surfaces.push(match surface {
                LiveSurface::Active(active) => HolonSurfaceImage::Active((**active).clone()),
                LiveSurface::Standing(standing) => {
                    HolonSurfaceImage::Standing((**standing).clone())
                }
                LiveSurface::Enacted(surface) => {
                    let ordinal = enacted
                        .iter()
                        .position(|candidate| Arc::ptr_eq(candidate, surface))
                        .ok_or(HolonError::RecoveryInvalid)?;
                    HolonSurfaceImage::Enacted(
                        u64::try_from(ordinal).map_err(|_| HolonError::PopulationOverflow)?,
                    )
                }
            });
        }
        let transitions = self
            .transitions
            .iter()
            .map(|transition| match transition {
                TransitionState::Open(open) => TransitionStateImage::Open(OpenTransitionImage {
                    roles: open.roles,
                    phase: open.phase,
                    residual_incidence_offset: open.residual_incidence_offset,
                    residual_incidences: open.residual_incidences,
                    provisional: open
                        .provisional
                        .map(|provisional| ProvisionalSettlementImage {
                            source_offset: provisional.source_offset,
                            sources: provisional.sources,
                            origin_offset: provisional.origin_offset,
                            origins: provisional.origins,
                            lineage_offset: provisional.lineage_offset,
                            lineages: provisional.lineages,
                        }),
                }),
                TransitionState::Closed {
                    receipt,
                    settlement,
                } => TransitionStateImage::Closed {
                    receipt: *receipt,
                    settlement: *settlement,
                },
                TransitionState::SettledSilent {
                    receipt,
                    settlement,
                } => TransitionStateImage::SettledSilent {
                    receipt: *receipt,
                    settlement: *settlement,
                },
            })
            .collect();
        Ok(LiveHolonImage {
            surfaces,
            cuts: self.cuts.clone(),
            transitions,
            receipts: self.receipts.clone(),
            silent_receipts: self.silent_receipts.clone(),
            settlements: self.settlements.clone(),
            source_dispositions: self.source_dispositions.clone(),
            return_origins: self.return_origins.clone(),
            lineage_incidences: self.lineage_incidences.clone(),
            residuals: self.residuals.clone(),
            residual_incidences: self.residual_incidences.clone(),
        })
    }

    pub(crate) fn from_checkpoint_image(
        image: LiveHolonImage,
        enacted: &[Arc<EnactedPopulation>],
    ) -> Result<Self, HolonError> {
        let mut surfaces = Vec::new();
        surfaces
            .try_reserve_exact(image.surfaces.len())
            .map_err(|_| HolonError::PopulationReservation)?;
        for surface in image.surfaces {
            surfaces.push(match surface {
                HolonSurfaceImage::Active(active) => {
                    active.validate().map_err(HolonError::SurfaceInvalid)?;
                    LiveSurface::Active(Arc::new(active))
                }
                HolonSurfaceImage::Standing(standing) => LiveSurface::Standing(Arc::new(standing)),
                HolonSurfaceImage::Enacted(ordinal) => LiveSurface::Enacted(
                    enacted
                        .get(usize::try_from(ordinal).map_err(|_| HolonError::RecoveryInvalid)?)
                        .cloned()
                        .ok_or(HolonError::RecoveryInvalid)?,
                ),
            });
        }
        let transitions = image
            .transitions
            .into_iter()
            .map(|transition| match transition {
                TransitionStateImage::Open(open) => TransitionState::Open(OpenTransition {
                    roles: open.roles,
                    phase: open.phase,
                    residual_incidence_offset: open.residual_incidence_offset,
                    residual_incidences: open.residual_incidences,
                    provisional: open.provisional.map(|provisional| ProvisionalSettlement {
                        source_offset: provisional.source_offset,
                        sources: provisional.sources,
                        origin_offset: provisional.origin_offset,
                        origins: provisional.origins,
                        lineage_offset: provisional.lineage_offset,
                        lineages: provisional.lineages,
                    }),
                }),
                TransitionStateImage::Closed {
                    receipt,
                    settlement,
                } => TransitionState::Closed {
                    receipt,
                    settlement,
                },
                TransitionStateImage::SettledSilent {
                    receipt,
                    settlement,
                } => TransitionState::SettledSilent {
                    receipt,
                    settlement,
                },
            })
            .collect();
        let holon = Self {
            surfaces,
            cuts: image.cuts,
            transitions,
            receipts: image.receipts,
            silent_receipts: image.silent_receipts,
            settlements: image.settlements,
            source_dispositions: image.source_dispositions,
            return_origins: image.return_origins,
            lineage_incidences: image.lineage_incidences,
            residuals: image.residuals,
            residual_incidences: image.residual_incidences,
        };
        holon.validate_checkpoint()?;
        Ok(holon)
    }

    fn validate_checkpoint(&self) -> Result<(), HolonError> {
        let span_is_bounded = |offset: u64, extent: u64, len: usize| {
            offset
                .checked_add(extent)
                .and_then(|after| usize::try_from(after).ok())
                .is_some_and(|after| after <= len)
                && (extent != 0 || offset == 0)
        };
        for cut in &self.cuts {
            let surface = self
                .surfaces
                .get(usize::try_from(cut.body()).map_err(|_| HolonError::RecoveryInvalid)?)
                .ok_or(HolonError::RecoveryInvalid)?;
            if cut.cut() >= surface.cuts() {
                return Err(HolonError::RecoveryInvalid);
            }
        }
        for (ordinal, transition) in self.transitions.iter().enumerate() {
            match transition {
                TransitionState::Open(open) => {
                    if !(3..=5).contains(&open.phase)
                        || open.roles[..usize::from(open.phase)].iter().any(|role| {
                            usize::try_from(*role).map_or(true, |role| role >= self.cuts.len())
                        })
                        || !span_is_bounded(
                            open.residual_incidence_offset,
                            open.residual_incidences,
                            self.residual_incidences.len(),
                        )
                        || (open.phase < 5 && open.provisional.is_some())
                        || (open.phase == 5 && open.provisional.is_none())
                    {
                        return Err(HolonError::RecoveryInvalid);
                    }
                    if let Some(provisional) = open.provisional {
                        if !span_is_bounded(
                            provisional.source_offset,
                            provisional.sources,
                            self.source_dispositions.len(),
                        ) || !span_is_bounded(
                            provisional.origin_offset,
                            provisional.origins,
                            self.return_origins.len(),
                        ) || !span_is_bounded(
                            provisional.lineage_offset,
                            provisional.lineages,
                            self.lineage_incidences.len(),
                        ) {
                            return Err(HolonError::RecoveryInvalid);
                        }
                    }
                }
                TransitionState::Closed {
                    receipt,
                    settlement,
                } => {
                    let receipt = self
                        .receipts
                        .get(usize::try_from(*receipt).map_err(|_| HolonError::RecoveryInvalid)?)
                        .ok_or(HolonError::RecoveryInvalid)?;
                    if [
                        receipt.before_cut(),
                        receipt.meeting_cut(),
                        receipt.deed_cut(),
                        receipt.consequence_cut(),
                        receipt.return_cut(),
                        receipt.after_cut(),
                    ]
                    .into_iter()
                    .any(|cut| usize::try_from(cut).map_or(true, |cut| cut >= self.cuts.len()))
                        || !span_is_bounded(
                            receipt.residual_incidence_offset(),
                            receipt.residual_incidences(),
                            self.residual_incidences.len(),
                        )
                    {
                        return Err(HolonError::RecoveryInvalid);
                    }
                    if let Some(settlement) = settlement {
                        let settlement = self
                            .settlements
                            .get(
                                usize::try_from(*settlement)
                                    .map_err(|_| HolonError::RecoveryInvalid)?,
                            )
                            .ok_or(HolonError::RecoveryInvalid)?;
                        if settlement.transition()
                            != u64::try_from(ordinal).map_err(|_| HolonError::PopulationOverflow)?
                        {
                            return Err(HolonError::RecoveryInvalid);
                        }
                    }
                }
                TransitionState::SettledSilent {
                    receipt,
                    settlement,
                } => {
                    let receipt = self
                        .silent_receipts
                        .get(usize::try_from(*receipt).map_err(|_| HolonError::RecoveryInvalid)?)
                        .ok_or(HolonError::RecoveryInvalid)?;
                    if [
                        receipt.before_cut(),
                        receipt.meeting_cut(),
                        receipt.deed_cut(),
                        receipt.after_cut(),
                    ]
                    .into_iter()
                    .any(|cut| usize::try_from(cut).map_or(true, |cut| cut >= self.cuts.len()))
                        || !span_is_bounded(
                            receipt.residual_incidence_offset(),
                            receipt.residual_incidences(),
                            self.residual_incidences.len(),
                        )
                    {
                        return Err(HolonError::RecoveryInvalid);
                    }
                    let settlement = self
                        .settlements
                        .get(
                            usize::try_from(*settlement)
                                .map_err(|_| HolonError::RecoveryInvalid)?,
                        )
                        .ok_or(HolonError::RecoveryInvalid)?;
                    if settlement.transition()
                        != u64::try_from(ordinal).map_err(|_| HolonError::PopulationOverflow)?
                    {
                        return Err(HolonError::RecoveryInvalid);
                    }
                }
            }
        }
        for settlement in &self.settlements {
            if usize::try_from(settlement.transition())
                .map_or(true, |transition| transition >= self.transitions.len())
                || !span_is_bounded(
                    settlement.source_offset(),
                    settlement.sources(),
                    self.source_dispositions.len(),
                )
                || !span_is_bounded(
                    settlement.origin_offset(),
                    settlement.origins(),
                    self.return_origins.len(),
                )
                || !span_is_bounded(
                    settlement.lineage_offset(),
                    settlement.lineages(),
                    self.lineage_incidences.len(),
                )
            {
                return Err(HolonError::RecoveryInvalid);
            }
        }
        if self
            .source_dispositions
            .iter()
            .any(|row| SourceDispositionRow::from_words(row.words()).is_none())
            || self
                .return_origins
                .iter()
                .any(|row| ReturnOriginRow::from_words(row.words()).is_none())
            || self
                .residuals
                .iter()
                .any(|row| ResidualSpan::from_words(row.words()).is_none())
            || self.residual_incidences.iter().any(|row| {
                usize::try_from(row.ordinal())
                    .map_or(true, |ordinal| ordinal >= self.residuals.len())
            })
        {
            return Err(HolonError::RecoveryInvalid);
        }
        for transition in &self.transitions {
            let (source_before, source, source_cut) = match transition {
                TransitionState::Open(open) => (
                    self.standing_at_role(open.roles[0])?,
                    self.enacted_at_role(open.roles[2])?,
                    self.cut_at_role(open.roles[2])?.cut(),
                ),
                TransitionState::Closed { receipt, .. } => {
                    let receipt = self
                        .receipts
                        .get(usize::try_from(*receipt).map_err(|_| HolonError::RecoveryInvalid)?)
                        .ok_or(HolonError::RecoveryInvalid)?;
                    (
                        self.standing_at_role(receipt.before_cut())?,
                        self.enacted_at_role(receipt.deed_cut())?,
                        self.cut_at_role(receipt.deed_cut())?.cut(),
                    )
                }
                TransitionState::SettledSilent { receipt, .. } => {
                    let receipt = self
                        .silent_receipts
                        .get(usize::try_from(*receipt).map_err(|_| HolonError::RecoveryInvalid)?)
                        .ok_or(HolonError::RecoveryInvalid)?;
                    (
                        self.standing_at_role(receipt.before_cut())?,
                        self.enacted_at_role(receipt.deed_cut())?,
                        self.cut_at_role(receipt.deed_cut())?.cut(),
                    )
                }
            };
            let source_successor =
                self.validate_prepared_successor(source, source_cut, source_before)?;
            match transition {
                TransitionState::Open(open) if open.phase == 5 => {
                    let returned = self.enacted_at_role(open.roles[4])?;
                    let return_cut = self.cut_at_role(open.roles[4])?.cut();
                    self.validate_prepared_successor(returned, return_cut, &source_successor)?;
                }
                TransitionState::Closed { receipt, .. } => {
                    let receipt = self
                        .receipts
                        .get(usize::try_from(*receipt).map_err(|_| HolonError::RecoveryInvalid)?)
                        .ok_or(HolonError::RecoveryInvalid)?;
                    let returned = self.enacted_at_role(receipt.return_cut())?;
                    let return_cut = self.cut_at_role(receipt.return_cut())?.cut();
                    let returned_successor =
                        self.validate_prepared_successor(returned, return_cut, &source_successor)?;
                    if self.standing_at_role(receipt.after_cut())? != returned_successor.as_ref() {
                        return Err(HolonError::RecoveryInvalid);
                    }
                }
                TransitionState::SettledSilent { receipt, .. } => {
                    let receipt = self
                        .silent_receipts
                        .get(usize::try_from(*receipt).map_err(|_| HolonError::RecoveryInvalid)?)
                        .ok_or(HolonError::RecoveryInvalid)?;
                    if self.standing_at_role(receipt.after_cut())? != source_successor.as_ref() {
                        return Err(HolonError::RecoveryInvalid);
                    }
                }
                TransitionState::Open(_) => {}
            }
        }
        Ok(())
    }

    fn cut_at_role(&self, role: u64) -> Result<BoundaryCut, HolonError> {
        self.cuts
            .get(usize::try_from(role).map_err(|_| HolonError::RecoveryInvalid)?)
            .copied()
            .ok_or(HolonError::RecoveryInvalid)
    }

    fn enacted_at_role(&self, role: u64) -> Result<&Arc<EnactedPopulation>, HolonError> {
        let cut = self.cut_at_role(role)?;
        self.surfaces
            .get(usize::try_from(cut.body()).map_err(|_| HolonError::RecoveryInvalid)?)
            .and_then(LiveSurface::enacted)
            .ok_or(HolonError::RecoveryInvalid)
    }

    fn standing_at_role(&self, role: u64) -> Result<&SparseStandingSurface, HolonError> {
        let cut = self.cut_at_role(role)?;
        self.surfaces
            .get(usize::try_from(cut.body()).map_err(|_| HolonError::RecoveryInvalid)?)
            .and_then(LiveSurface::standing)
            .map(Arc::as_ref)
            .ok_or(HolonError::RecoveryInvalid)
    }

    fn validate_prepared_successor(
        &self,
        enacted: &Arc<EnactedPopulation>,
        cut: u64,
        before: &SparseStandingSurface,
    ) -> Result<Arc<SparseStandingSurface>, HolonError> {
        let prepared = enacted
            .prepared_cut(cut)
            .ok_or(HolonError::RecoveryInvalid)?;
        let folded = prepare_sparse_fold_from_owned(
            enacted.active(),
            enacted.carried(),
            enacted.incidence_surface_index(),
            enacted.directed_contacts(),
            cut,
            before,
        )
        .map_err(|_| HolonError::RecoveryInvalid)?;
        if &folded != prepared.fold() {
            return Err(HolonError::RecoveryInvalid);
        }
        let successor = before
            .prepare_successor(&folded)
            .map_err(|_| HolonError::RecoveryInvalid)?;
        let retained = prepared.successor().ok_or(HolonError::RecoveryInvalid)?;
        if &successor != retained {
            return Err(HolonError::RecoveryInvalid);
        }
        Ok(Arc::new(successor))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use body::num::Cog;
    use soma_abi::active::{
        ActionCurrent, CurrentSpan, CutSpan, EventSpan, Incidence, OriginRef, RelationAtom,
    };

    fn surface(value: i64, organ: u64) -> Arc<ActiveCut> {
        Arc::new(
            ActiveCut::new(
                vec![RelationAtom::new(Cog::lit(value)).unwrap()],
                vec![EventSpan::new(0, 1).unwrap()],
                vec![ActionCurrent::new(Cog::lit(value.abs() + 1)).unwrap()],
                vec![OriginRef::new(organ, 0)],
                vec![CurrentSpan::new(0, 1, 0, 1).unwrap()],
                vec![CutSpan::new(0, 1, 0, 0).unwrap()],
                vec![Incidence::new(0, 0, 1).unwrap()],
                Vec::new(),
            )
            .unwrap(),
        )
    }

    #[test]
    fn a_transition_stays_open_and_cannot_skip_a_lived_role() {
        let mut holon = LiveHolon::new();
        let before_surface = holon.mount(surface(2, 1)).unwrap();
        let meeting_surface = holon.mount(surface(3, 2)).unwrap();
        let before = holon.cut(before_surface, 0).unwrap();
        let meeting = holon.cut(meeting_surface, 0).unwrap();
        let transition = holon.begin(before).unwrap();
        assert_eq!(holon.phase(transition), Ok(1));
        assert_eq!(
            holon.deed(transition, meeting),
            Err(HolonError::WrongPhase {
                expected: 2,
                actual: 1
            })
        );
        assert!(holon.receipts.is_empty());
        holon.meeting(transition, meeting).unwrap();
        assert_eq!(holon.phase(transition), Ok(2));
        assert!(holon.receipts.is_empty());
    }

    #[test]
    fn six_actual_cuts_close_one_live_receipt_and_retain_the_return_surface() {
        let mut holon = LiveHolon::new();
        let ids = [
            holon.mount(surface(2, 0)).unwrap(),
            holon.mount(surface(3, 1)).unwrap(),
            holon.mount(surface(5, 2)).unwrap(),
            holon.mount(surface(7, 3)).unwrap(),
            holon.mount(surface(11, 4)).unwrap(),
            holon.mount(surface(13, 5)).unwrap(),
        ];
        let cuts = ids.map(|id| holon.cut(id, 0).unwrap());
        let transition = holon.begin(cuts[0]).unwrap();
        holon.meeting(transition, cuts[1]).unwrap();
        holon.deed(transition, cuts[2]).unwrap();
        holon.consequence(transition, cuts[3]).unwrap();
        holon.retain_residual(transition, cuts[3], 0, 1).unwrap();
        holon.returned(transition, cuts[4]).unwrap();
        let receipt = holon.after(transition, cuts[5]).unwrap();

        assert_eq!(
            [
                receipt.before_cut(),
                receipt.meeting_cut(),
                receipt.deed_cut(),
                receipt.consequence_cut(),
                receipt.return_cut(),
                receipt.after_cut(),
            ],
            [0, 1, 2, 3, 4, 5],
            "one mounted cut stands once while residual and role references remain plural"
        );
        assert_eq!(receipt.residual_incidences(), 1);
        assert_eq!(holon.phase(transition), Err(HolonError::TransitionClosed));
        let returned = holon.surface(ids[4]).unwrap().active().unwrap();
        assert_eq!(returned.atoms[0].cog(), Cog::lit(11));
    }
}
