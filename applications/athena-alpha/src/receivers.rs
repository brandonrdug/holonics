use life::native_intelligence::{
    NativeCirculationBoundary, NativeCirculationSnapshot, NativeMorphologyCommit,
};
use serde::Serialize;

use crate::ATHENA_ALPHA_APPLICATION_SCHEMA;

/// Exact exterior inspection of one complete alpha cycle. This is a receiver, not native state.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AthenaAlphaCycleReceipt {
    pub schema: String,
    pub predecessor_generation: u64,
    pub successor_generation: u64,
    pub returned_occurrence: holonic_engine::EventId,
    pub causal_cone_population: usize,
    pub interchange_population: usize,
    pub reconstruction_fibre_population: usize,
    pub later_boundary: NativeCirculationBoundary,
    pub snapshot_generation: u64,
    pub snapshot_commit_population: usize,
    pub snapshot_package_octets: usize,
    pub remount_generation: u64,
    pub source_neutral_runtime: bool,
}

pub fn inspect_cycle(
    commit: &NativeMorphologyCommit,
    later_boundary: NativeCirculationBoundary,
    snapshot: &NativeCirculationSnapshot,
    remount_generation: u64,
) -> AthenaAlphaCycleReceipt {
    AthenaAlphaCycleReceipt {
        schema: ATHENA_ALPHA_APPLICATION_SCHEMA.to_owned(),
        predecessor_generation: commit.predecessor_lineage.generation,
        successor_generation: commit.successor_lineage.generation,
        returned_occurrence: commit.returned_occurrence,
        causal_cone_population: commit.causal_cone.len(),
        interchange_population: commit.interchange_population,
        reconstruction_fibre_population: commit.reconstruction_fibre_population,
        later_boundary,
        snapshot_generation: commit.successor_lineage.generation,
        snapshot_commit_population: snapshot.commits.len(),
        snapshot_package_octets: snapshot.package_wire.len(),
        remount_generation,
        source_neutral_runtime: true,
    }
}
