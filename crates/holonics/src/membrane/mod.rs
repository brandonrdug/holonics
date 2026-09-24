//! The live, organ-neutral receiving and standing runtime.
//!
//! Source organs turn encountered material into native relation atoms and event actions.
//! [`LiveCurrentMachine`] owns the continuing standing topology and live current carriers;
//! [`SparseStandingSurface`] is its concrete storage chart. The general standing law belongs
//! to the Holon/restriction owners. This module has no source-organ, renderer or corpus dependency.
//! Its former `soma-membrane` package and the already retired historical replay namespace are
//! recorded in `docs/plans/census/R2_MEMBRANE_EDGE.md`.

pub mod chart_address;
pub mod growing_carrier;
pub mod growing_ranked;
pub mod growing_sparse;
pub mod live_carrier;
pub mod live_constituent;
pub mod live_current;
pub mod sparse_standing;
mod support_family;

pub use chart_address::{ChartAddress, ChartAddressError};
pub use growing_carrier::GrowingCarrier;
pub use growing_ranked::{GrowingRankedOwn, RankedOwnCell};
pub use growing_sparse::GrowingSparseOwn;
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
    ContemporaryEvent, ContemporaryRadiation, CpuLiveCurrentExecutor, CurrentBodyMount,
    CurrentBoundaryPort, CurrentEvent, CurrentExecutionRequest, CurrentGeometry, CurrentLineage,
    CurrentRadiation, DirectedCurrentRelation, DirectedExecutionRequest, DirectedRelationRadiation,
    EventIncidenceRadiation, EventNodeAtlas, ExecutedContemporaryEvent, ExecutedDirectedRelation,
    ExecutedLiveCurrent, ExecutedRegionalRelation, LiveCurrentError, LiveCurrentExecutor,
    LiveCurrentMachine, LiveCurrentRestImage, LiveLineageRestImage, LiveMemory,
    ParallelCpuLiveCurrentExecutor, ReceiverCausalPassage, ReceiverCausalPassageError,
    ReceiverChartIdentity, RegionalArcExecution, RegionalArcRadiation, RegionalExecutionRequest,
    RegionalRelationArc, RegionalRelationCell, RegionalRelationRadiation, RegionalSupportSection,
    LIVE_CURRENT_REST_LAYOUT_VERSION,
};
pub use sparse_standing::{SparseStandingError, SparseStandingSurface, StandingCell};
pub use support_family::{LiveSupportFamily, LiveSupportSection, SupportFamilyError};
