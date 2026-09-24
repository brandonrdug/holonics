//! Process-scoped configuration for the CUDA refinement trace receivers.
//!
//! These flags are apparatus controls, so their environment snapshot is taken once per process.
//! Keeping the snapshot in one typed owner also makes every downstream receiver observe the same
//! configuration throughout a run.

use std::sync::OnceLock;

/// The six refinement and membrane instrumentation switches read at process startup/use.
#[derive(Clone, Copy, Debug, Default)]
pub struct TraceConfiguration {
    pub holonics_phase_trace: bool,
    pub holonics_profile_sync: bool,
    pub holonics_uar2_trace: bool,
    pub holonics_uar2_conformance: bool,
    pub mem6_cuda_profile: bool,
    pub mem6_causal_profile: bool,
}

static CONFIGURATION: OnceLock<TraceConfiguration> = OnceLock::new();

/// Return the cached process configuration.
pub fn trace_configuration() -> &'static TraceConfiguration {
    CONFIGURATION.get_or_init(|| TraceConfiguration {
        holonics_phase_trace: std::env::var_os("HOLONICS_PHASE_TRACE").is_some(),
        holonics_profile_sync: std::env::var_os("HOLONICS_PROFILE_SYNC").is_some(),
        holonics_uar2_trace: std::env::var_os("HOLONICS_UAR2_TRACE").is_some(),
        holonics_uar2_conformance: std::env::var_os("HOLONICS_UAR2_CONFORMANCE").is_some(),
        mem6_cuda_profile: std::env::var_os("MEM6_CUDA_PROFILE").is_some(),
        mem6_causal_profile: std::env::var_os("MEM6_CAUSAL_PROFILE").is_some(),
    })
}
