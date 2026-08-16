//! The live, organ-neutral execution membrane.
//!
//! Source organs own their material grains and transform encountered world material into native
//! relation atoms and event actions. [`LiveCurrentMachine`] is the production lifetime owner: it
//! retains standing topology and genuinely live current carriers only. This crate has no text,
//! filesystem, image, renderer, corpus, scheduler, or semantic dependency.
//!
//! **The `historical` namespace was removed 2026-08-15.** It re-exported eleven modules —
//! `active_cut`, `active_topology`, `co_present`, `contact_cycle`, `cut_surface`,
//! `directed_contact`, `emission_journal`, `event_mouth`, `event_surface`, `live_holon`,
//! `recovery` — 11,214 of this crate's then 27,104 lines, declaring of itself that they "do not
//! feed, reconstruct, or own [`LiveCurrentMachine`]". They did not: `grep -rn "historical::"
//! crates soma --include='*.rs'` returned zero outside the declaration, none of the eighty-two
//! names it exported occurred anywhere outside `soma/membrane/src/`, and the eleven referenced
//! only each other — the single edge into a live module was
//! `sparse_standing::prepare_successor`, whose own callers were all inside the island. A retired
//! interface is refused rather than deprecated, and git history is the recovery surface
//! (`CLAUDE.md` §13 rule 3). They are recoverable at `09b55d9` and earlier.

pub mod chart_address;
pub mod growing_carrier;
pub mod growing_ranked;
pub mod growing_sparse;
pub mod live_carrier;
pub mod live_constituent;
pub mod live_current;
pub mod ranked_surface;
pub mod sparse_standing;
pub mod sparse_surface;
mod support_family;

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
