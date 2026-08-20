use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::causal::EventId;
use crate::evolution::EvolutionLawId;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoverageReceipt {
    pub source_occurrences: usize,
    pub native_occurrences: usize,
    pub open_occurrences: usize,
    pub source_populations: usize,
    pub native_populations: usize,
    pub open_populations: usize,
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum CorrespondenceRefusal {
    #[error("a source deed must have a non-empty identity")]
    EmptyDeed,
    #[error("a source operation family must have a non-empty identity")]
    EmptyFamily,
    #[error("source event {event:?} names missing operation law {law:?}")]
    MissingOperation { event: EventId, law: EvolutionLawId },
    #[error("source event {event:?} names missing law declaration {law:?}")]
    MissingLaw { event: EventId, law: EvolutionLawId },
    #[error("source event {event:?} names missing boundary {boundary} on law {law:?}")]
    MissingBoundary {
        event: EventId,
        law: EvolutionLawId,
        boundary: u64,
    },
    #[error("source occurrence {source_id:?} is missing a correspondence")]
    MissingOccurrence { source_id: String },
    #[error("source occurrence {source_id:?} has duplicate correspondence records")]
    DuplicateOccurrence { source_id: String },
    #[error("correspondence names foreign source occurrence {source_id:?}")]
    ForeignOccurrence { source_id: String },
    #[error("binding id {binding_id:?} disagrees with source occurrence {source_id:?}")]
    BindingIdDisagrees {
        source_id: String,
        binding_id: String,
    },
    #[error("source occurrence {source_id:?} has an empty open remainder")]
    EmptyRemainder { source_id: String },
    #[error(
        "source occurrence {source_id:?} has a native binding with an incomplete identity: {reason}"
    )]
    IncompleteNativeBinding { source_id: String, reason: String },
    #[error("native binding for {source_id:?} disagrees with source arity/species: {reason}")]
    NativeBindingDisagrees { source_id: String, reason: String },
    #[error(
        "source operation {source_id:?} names carrier population {source_population:?}, which is absent from the population closure"
    )]
    CarrierPopulationUnlisted {
        source_id: String,
        source_population: String,
    },
    #[error(
        "source operation {source_id:?} carrier population {source_population:?} has no native population"
    )]
    CarrierPopulationNotNative {
        source_id: String,
        source_population: String,
    },
    #[error(
        "native binding for {source_id:?} does not carry the source carrier's native population"
    )]
    CarrierPopulationMissing { source_id: String },
    #[error(
        "native binding for {source_id:?} names a native population but the source occurrence has no carrier"
    )]
    UnexpectedCarrierPopulation { source_id: String },
    #[error("native graph identity for {source_id:?} is not derived from its graph receipt")]
    GraphIdentityNotDerived { source_id: String },
    #[error(
        "native graph identity for {source_id:?} carries counts but no operation topology/chronology"
    )]
    GraphTopologyAbsent { source_id: String },
    #[error("native graph registry contains duplicate identity {graph_key:?}")]
    DuplicateGraphIdentity { graph_key: String },
    #[error("native graph registry is missing binding {source_id:?}'s graph {graph_key:?}")]
    GraphIdentityMissing {
        source_id: String,
        graph_key: String,
    },
    #[error("native graph identity {graph_key:?} is incomplete: {reason}")]
    IncompleteGraphIdentity { graph_key: String, reason: String },
    #[error("source occurrence {source_id:?} is duplicated in the admitted source closure")]
    DuplicateSourceOccurrence { source_id: String },
    #[error("source occurrence {source_id:?} has no topology identity in its stable id")]
    MissingSourceIdentity { source_id: String },
    #[error("source population {source_population:?} is empty")]
    EmptySourcePopulation { source_population: String },
    #[error("source population {source_population:?} is duplicated in the admitted source closure")]
    DuplicateSourcePopulation { source_population: String },
    #[error("source population {source_population:?} is missing a disposition")]
    MissingPopulation { source_population: String },
    #[error("source population {source_population:?} has duplicate disposition records")]
    DuplicatePopulation { source_population: String },
    #[error("disposition names foreign source population {source_population:?}")]
    ForeignPopulation { source_population: String },
    #[error("native population for {source_population:?} is empty")]
    EmptyNativePopulation { source_population: String },
    #[error("open remainder {name:?} has an empty reason or reopening route")]
    InvalidRemainder { name: String },
    #[error("correspondence schema {found:?} is not the admitted {expected:?}")]
    WrongSchema { expected: String, found: String },
    #[error("correspondence JSON is malformed: {reason}")]
    InvalidJson { reason: String },
}
