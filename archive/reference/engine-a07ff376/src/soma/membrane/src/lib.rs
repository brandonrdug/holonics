//! The live, organ-neutral execution membrane.
//!
//! Source organs own their material grains and transform encountered world material into native
//! relation atoms and event actions. [`LiveCurrentMachine`] is the production lifetime owner: it
//! retains standing topology and genuinely live current carriers only. Historical active-cut,
//! Holon, journal, and ecology testimony is available only through [`historical`]; it is not a
//! second production mouth. This crate has no text, filesystem, image, renderer, corpus,
//! scheduler, or semantic dependency.

mod active_cut;
mod active_topology;
pub mod chart_address;
mod co_present;
mod contact_cycle;
mod cut_surface;
mod directed_contact;
mod emission_journal;
mod event_mouth;
mod event_surface;
pub mod growing_carrier;
pub mod growing_ranked;
pub mod growing_sparse;
pub mod live_carrier;
pub mod live_constituent;
pub mod live_current;
mod live_holon;
pub mod ranked_surface;
mod recovery;
pub mod sparse_standing;
pub mod sparse_surface;
mod support_family;

// Historical implementation modules still share these names internally. Crate visibility keeps
// that source intact without presenting a second causal owner at the public root.
pub(crate) use active_cut::{ActiveCut, ActiveCutError, ValidatedActiveCut};
pub(crate) use active_topology::{CarriedSpanSurface, FoldedCut};
pub(crate) use contact_cycle::{EcologyId, EnactedPopulation, LineageHandle};
pub(crate) use cut_surface::CutSurfaceError;
pub(crate) use directed_contact::{DirectedCutContact, DirectedResolution};
pub(crate) use emission_journal::{
    CurrentEmissionBuilder, EmissionJournal, EmissionJournalBuilder, EmissionJournalError,
};
#[cfg(test)]
pub(crate) use event_mouth::{conduct_current_emitting, preflight_active_deeds};
pub(crate) use event_mouth::{ConductError, CurrentConduct, EventContact};
pub(crate) use event_surface::{EventSurface, EventSurfaceError, EventTopology};
#[cfg(test)]
pub(crate) use live_holon::LiveSurfaceKind;
pub(crate) use live_holon::{HolonError, LiveHolon, TransitionId, TransitionStatus};
pub(crate) use recovery::{
    HolonSurfaceImage, LiveHolonImage, OpenTransitionImage, ProvisionalSettlementImage,
    TransitionStateImage,
};

pub use chart_address::{ChartAddress, ChartAddressError};
pub use growing_carrier::GrowingCarrier;
pub use growing_ranked::{GrowingRankedOwn, RankedOwnCell};
pub use growing_sparse::GrowingSparseOwn;
pub use holonic_structure::CausalMembrane;
pub use live_carrier::{LiveCarrierError, LiveCarrierSnapshot};
pub use live_constituent::{
    BoundaryBehavior, CompressionCertificate, FormedPin, InterfaceCapability,
    InterfaceCapabilityOrigin, InterfaceWitness, LiveBoundary, LiveBoundaryTransition, LiveCell,
    LiveConstituent, LiveConstituentError, LiveIncidence, LiveIncidenceKind, LivePath,
    LivePathStep, LivePin, LocalAxis, LocalBlade, ParallelPathComparison, ReceiverFiberIdentity,
    SparseTransport, TransportTerm,
};
pub use live_current::{
    canonical_event_incidences, form_executed_regional_relation, regional_contact_pairs,
    ContemporaryEvent, ContemporaryRadiation, CurrentBodyMount, CurrentBoundaryPort, CurrentEvent,
    CurrentExecutionRequest, CurrentGeometry, CurrentLineage, CurrentRadiation,
    DirectedCurrentRelation, DirectedExecutionRequest, DirectedRelationRadiation,
    EventIncidenceRadiation, EventNodeAtlas, ExecutedContemporaryEvent, ExecutedDirectedRelation,
    ExecutedLiveCurrent, ExecutedRegionalRelation, HostLiveCurrentExecutor, LiveCurrentError,
    LiveCurrentExecutor, LiveCurrentMachine, LiveCurrentRestImage, LiveLineageRestImage,
    LiveMemory, ParallelHostLiveCurrentExecutor, ReceiverCausalPassage, ReceiverCausalPassageError,
    ReceiverChartIdentity, RegionalArcExecution, RegionalArcRadiation, RegionalExecutionRequest,
    RegionalRelationArc, RegionalRelationCell, RegionalRelationRadiation, RegionalSupportSection,
    LIVE_CURRENT_REST_LAYOUT_VERSION,
};
pub use ranked_surface::{RankedFeltSurface, RankedSurfaceError};
pub use sparse_standing::{SparseStandingError, SparseStandingSurface, StandingCell};
pub use sparse_surface::{SparseFeltCell, SparseFeltSurface, SparseSurfaceError};
pub use support_family::{LiveSupportFamily, LiveSupportSection, SupportFamilyError};

/// Historical active-cut, contact-cycle, Holon, journal, and recovery apparatus.
///
/// These types preserve exact prior measurements and observer/recovery surfaces. They may be used
/// by historical instruments, but they do not feed, reconstruct, or own [`LiveCurrentMachine`].
pub mod historical {
    pub use crate::active_cut::{ActiveCut, ActiveCutError, RowFamily, ValidatedActiveCut};
    pub use crate::active_topology::{
        ActiveTopology, ActiveTopologyError, CarriedCell, CarriedSpanSurface, FoldedCell, FoldedCut,
    };
    pub use crate::co_present::{
        compose_selected_cuts, CoPresentCut, ComposeCutError, CutEmbedding, RowRange, SelectedCut,
    };
    pub use crate::contact_cycle::{
        CarriedCutRef, ClosedContact, ContactCycleError, CurrentContactState, CurrentMount,
        CurrentOutcome, EcologyId, EcologyRestImage, EnactedPopulation, LineageHandle,
        LineageImage, LineageIncidence, LineageRef, LiveEcology, OpenContact, PendingAfterContact,
        PreparedContact, PreparedCut, ReturnOrigin, SettlementPlan, SilentContact,
        SourceDisposition, TransitionContact,
    };
    pub use crate::cut_surface::{CutSurface, CutSurfaceError, IncidenceSurface};
    pub use crate::directed_contact::{DirectedCutContact, DirectedResolution};
    pub use crate::emission_journal::{
        CurrentEmissionBuilder, CurrentEmissionPart, EmissionJournal, EmissionJournalBuilder,
        EmissionJournalError,
    };
    pub use crate::event_mouth::{
        conduct_current, conduct_current_emitting, conduct_current_partition,
        preflight_active_deeds, preflight_current, preflight_current_partition, ConductError,
        CurrentConduct, CurrentPreflight, EventContact,
    };
    pub use crate::event_surface::{
        DirectedEventSurface, EventSurface, EventSurfaceError, EventTopology, IncidenceEventSurface,
    };
    pub use crate::live_holon::{
        CutRef, HolonError, LiveHolon, LiveSurface, LiveSurfaceKind, SurfaceId, TransitionId,
        TransitionStatus,
    };
    pub use crate::recovery::{
        CurrentMountImage, CurrentOutcomeImage, EcologyCheckpoint, EnactedPopulationImage,
        HolonSurfaceImage, LineageStateImage, LiveHolonImage, OpenTransitionImage,
        PreparedCutImage, ProvisionalSettlementImage, TransitionStateImage,
        ECOLOGY_CHECKPOINT_VERSION,
    };
}
