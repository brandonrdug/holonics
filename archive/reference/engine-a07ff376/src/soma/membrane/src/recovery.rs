//! Exact typed recovery testimony for one living, source-neutral ecology.
//!
//! These rows describe active relational construction. They are never presented to Soma as
//! source light, and they contain no material-world, text, file, renderer, scheduler, or device
//! vocabulary. Recovery validates and rebinds the graph so one durable lineage or enactment again
//! has one shared live owner while temporally distinct equal-valued surfaces remain distinct.

use body::manifold::TermCounts;
use soma_abi::holon::{
    BoundaryCut, LineageIncidenceRow, ResidualIncidence, ResidualSpan, ReturnOriginRow,
    SettlementSpan, SilentReceipt, SourceDispositionRow, TransitionReceipt,
};

use crate::{
    ActiveCut, CarriedSpanSurface, CurrentConduct, DirectedCutContact, EcologyId, EmissionJournal,
    EventContact, EventSurface, FoldedCut, LineageHandle, RankedOwnCell, SparseStandingSurface,
};

pub const ECOLOGY_CHECKPOINT_VERSION: u32 = 1;

/// One complete current-local consequence retained without a live pointer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CurrentOutcomeImage {
    pub(crate) conduct: CurrentConduct,
    pub(crate) contacts: Vec<EventContact>,
    pub(crate) own_rank: u64,
    pub(crate) own_occupancy: Vec<u64>,
    pub(crate) breath: (u64, u64),
    pub(crate) own_cells: Vec<RankedOwnCell>,
    pub(crate) terms: TermCounts,
    pub(crate) native_carrier: Vec<u32>,
    pub(crate) thoughts: u32,
}

impl CurrentOutcomeImage {
    pub fn conduct(&self) -> CurrentConduct {
        self.conduct
    }

    pub fn contacts(&self) -> &[EventContact] {
        &self.contacts
    }

    pub fn native_carrier_words(&self) -> &[u32] {
        &self.native_carrier
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedCutImage {
    pub(crate) cut: u64,
    pub(crate) fold: FoldedCut,
    pub(crate) successor: SparseStandingSurface,
}

/// A mount records only its exact live ancestry. `Birth` and `Continue` are physical provenance,
/// not a content classification.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CurrentMountImage {
    Birth,
    Continue(LineageHandle),
}

/// One canonical lineage state. Its carrier is the current outcome at `handle`; storing that body
/// twice would create two authorities for one first person.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LineageStateImage {
    pub(crate) handle: LineageHandle,
    pub(crate) parents: Vec<LineageHandle>,
    pub(crate) claimed: bool,
}

impl LineageStateImage {
    pub fn handle(&self) -> LineageHandle {
        self.handle
    }

    pub fn parents(&self) -> &[LineageHandle] {
        &self.parents
    }

    pub fn claimed(&self) -> bool {
        self.claimed
    }
}

/// Complete enacted population at one enactment ordinal. Every derived lookup remains beside the
/// exact topology so recovery can validate it instead of replaying source conduct.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnactedPopulationImage {
    pub(crate) enactment: u64,
    pub(crate) active: ActiveCut,
    pub(crate) event_surfaces: Vec<EventSurface>,
    pub(crate) emissions: EmissionJournal,
    pub(crate) currents: Vec<CurrentOutcomeImage>,
    pub(crate) carried: Vec<CarriedSpanSurface>,
    pub(crate) incidence_surface: Vec<u64>,
    pub(crate) directed_contacts: Vec<DirectedCutContact>,
    pub(crate) prepared_cut: Option<PreparedCutImage>,
    pub(crate) mounts: Vec<CurrentMountImage>,
    pub(crate) lineages: Vec<LineageStateImage>,
}

impl EnactedPopulationImage {
    pub fn enactment(&self) -> u64 {
        self.enactment
    }

    pub fn active(&self) -> &ActiveCut {
        &self.active
    }

    pub fn currents(&self) -> &[CurrentOutcomeImage] {
        &self.currents
    }

    pub fn lineages(&self) -> &[LineageStateImage] {
        &self.lineages
    }
}

/// Surface occurrence in append order. An enacted row names the ecology's canonical enactment;
/// active and standing occurrences remain owned values because two equal faces at different times
/// are not one occurrence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HolonSurfaceImage {
    Active(ActiveCut),
    Standing(SparseStandingSurface),
    Enacted(u64),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProvisionalSettlementImage {
    pub(crate) source_offset: u64,
    pub(crate) sources: u64,
    pub(crate) origin_offset: u64,
    pub(crate) origins: u64,
    pub(crate) lineage_offset: u64,
    pub(crate) lineages: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpenTransitionImage {
    pub(crate) roles: [u64; 6],
    pub(crate) phase: u8,
    pub(crate) residual_incidence_offset: u64,
    pub(crate) residual_incidences: u64,
    pub(crate) provisional: Option<ProvisionalSettlementImage>,
}

impl OpenTransitionImage {
    pub fn phase(&self) -> u8 {
        self.phase
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TransitionStateImage {
    Open(OpenTransitionImage),
    Closed {
        receipt: u64,
        settlement: Option<u64>,
    },
    SettledSilent {
        receipt: u64,
        settlement: u64,
    },
}

/// Every row needed to recover the live six-role boundary without reconstructing it from receipts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LiveHolonImage {
    pub(crate) surfaces: Vec<HolonSurfaceImage>,
    pub(crate) cuts: Vec<BoundaryCut>,
    pub(crate) transitions: Vec<TransitionStateImage>,
    pub(crate) receipts: Vec<TransitionReceipt>,
    pub(crate) silent_receipts: Vec<SilentReceipt>,
    pub(crate) settlements: Vec<SettlementSpan>,
    pub(crate) source_dispositions: Vec<SourceDispositionRow>,
    pub(crate) return_origins: Vec<ReturnOriginRow>,
    pub(crate) lineage_incidences: Vec<LineageIncidenceRow>,
    pub(crate) residuals: Vec<ResidualSpan>,
    pub(crate) residual_incidences: Vec<ResidualIncidence>,
}

impl LiveHolonImage {
    pub fn transitions(&self) -> &[TransitionStateImage] {
        &self.transitions
    }

    pub fn surfaces(&self) -> &[HolonSurfaceImage] {
        &self.surfaces
    }
}

/// One complete ecology at any committed lifecycle phase. The schema is typed and in-memory here;
/// a durable substrate may encode these rows independently, but that encoding remains testimony
/// and may never be fed back through the active mouth.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EcologyCheckpoint {
    pub(crate) version: u32,
    pub(crate) id: EcologyId,
    pub(crate) generation: u64,
    pub(crate) next_enactment: u64,
    pub(crate) standing: SparseStandingSurface,
    pub(crate) enacted: Vec<EnactedPopulationImage>,
    pub(crate) holon: LiveHolonImage,
}

impl EcologyCheckpoint {
    pub fn version(&self) -> u32 {
        self.version
    }

    pub fn id(&self) -> EcologyId {
        self.id
    }

    pub fn generation(&self) -> u64 {
        self.generation
    }

    pub fn standing(&self) -> &SparseStandingSurface {
        &self.standing
    }

    pub fn enacted(&self) -> &[EnactedPopulationImage] {
        &self.enacted
    }

    pub fn holon(&self) -> &LiveHolonImage {
        &self.holon
    }
}
