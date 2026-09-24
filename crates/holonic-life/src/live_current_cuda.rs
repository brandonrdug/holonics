//! Resident CUDA execution owner for the live-current membrane.
//!
//! One context and one module remain mounted. One parallel contact launch per receiving current
//! forms its immutable standing-before field; one lineage launch then changes that current's sole
//! mutable carrier. Reusable physical apertures grow after actual pressure and retry from the
//! unchanged predecessor. No active cut, dataset, journal, receipt, or ancestry population is
//! allocated on the card.

use std::collections::BTreeMap;

use ::holonics_cuda::{
    Context, Device, DeviceBuffer, LaunchEvidence, LiveEventArguments, LiveEventSpan,
    LiveEventWriteSpan, Module, RegionalContactArguments, SOMA_PTX,
};
use holonics_portable::manifold::{
    node_packed_word, LiveBodyHeader, SparseOwnCell, CARRIER_HEADER_WORDS, ENCLOSURE_WORDS,
    NODE_WORDS,
};
use holonics_portable::medium::FORM_WORDS;
use holonics_portable::num::COG_WORDS;
use soma_abi::emission::{DeedEmission, DEED_WORDS};
use soma_abi::live_event_cuda as cuda;
use holonics::membrane::{
    canonical_event_incidences, form_executed_regional_relation, regional_contact_pairs,
    CurrentExecutionRequest, CurrentGeometry, CurrentLineage, DirectedExecutionRequest,
    EventIncidenceRadiation, ExecutedContemporaryEvent, ExecutedDirectedRelation,
    ExecutedLiveCurrent, ExecutedRegionalRelation, GrowingCarrier, LiveCarrierSnapshot,
    LiveCurrentError, LiveCurrentExecutor, RankedOwnCell, RegionalExecutionRequest,
    SparseStandingSurface,
};

mod executor;
mod mount;
mod receipt;
#[cfg(test)]
mod tests;

use self::mount::*;

/// One resident CUDA context/module.  The context is last so every module/allocation drops first.
pub struct CudaLiveCurrentExecutor {
    pub(crate) module: Module,
    device_name: String,
    stack_limit_bytes: usize,
    stack_growths: u64,
    launches: u64,
    contact_launches: u64,
    parallel_contact_lanes: u64,
    resource_retries: u64,
    directed_contacts: u64,
    standing_full_mounts: u64,
    carrier_full_mounts: u64,
    standing_cpu_words: u64,
    standing_device_words: u64,
    carrier_cpu_words: u64,
    carrier_device_words: u64,
    resident_body_key: Option<usize>,
    resident_revision: Option<u64>,
    resident_standing: Option<ResidentStanding>,
    resident_lineages: BTreeMap<CurrentLineage, ResidentCarrier>,
    staged: Option<StagedEvent>,
    /// **The device's own launch census**, taken once at mount: `μ`'s `D` constituent, and the
    /// source of the reported multiprocessor population. It is no longer the *launch evidence* of
    /// any mouth: a census carries neither the per-dimension block extent nor the per-block shared
    /// extent nor the warp, so every mouth crossed with it deferred those clauses.
    launch_census: Option<::holonics_cuda::cuda::LaunchCensus>,
    /// **The mounted card's own handle**, retained from mount and presented as
    /// `LaunchEvidence::Device` at every launch this executor issues, so no clause of any of them
    /// is deferred. The launch *shape* is still derived from the card, never authored.
    device: Device,
    max_blocks_per_multiprocessor: u32,
    concurrent_kernels: bool,
    pub(crate) context: Context,
}

impl CudaLiveCurrentExecutor {
    pub fn new(device_ordinal: i32) -> ::holonics_cuda::Result<Self> {
        ::holonics_cuda::cuda::init()?;
        let device = Device::get(device_ordinal)?;
        let launch_census = Some(device.launch_census()?);
        let max_blocks_per_multiprocessor = u32::try_from(
            device.attribute(::holonics_cuda::DeviceAttribute::MAX_BLOCKS_PER_MULTIPROCESSOR)?,
        )
        .ok()
        .filter(|value| *value > 0)
        .ok_or_else(|| ::holonics_cuda::CudaError {
            code: -1,
            name: String::from("LIVE_EVENT_BLOCK_RESIDENCY"),
            message: String::from("the device reported no resident block aperture"),
            context: "CudaLiveCurrentExecutor::new",
        })?;
        let concurrent_kernels =
            device.attribute(::holonics_cuda::DeviceAttribute::CONCURRENT_KERNELS)? != 0;
        let context = Context::create(&device)?;
        let module = Module::load_ptx(SOMA_PTX)?;
        let local = module.lineage_event()?.local_size_bytes()?;
        let stack = local
            .max(LIVE_EVENT_STACK_MIN_BYTES)
            .checked_next_power_of_two()
            .ok_or_else(|| ::holonics_cuda::CudaError {
                code: -1,
                name: String::from("LIVE_EVENT_STACK_EXTENT"),
                message: String::from("lineage_event local-memory extent cannot be rounded"),
                context: "CudaLiveCurrentExecutor::new",
            })?;
        let stack_limit_bytes = context.ensure_stack_limit_bytes(stack)?;
        Ok(Self {
            module,
            device_name: device.name.clone(),
            stack_limit_bytes,
            stack_growths: 0,
            launches: 0,
            contact_launches: 0,
            parallel_contact_lanes: 0,
            resource_retries: 0,
            directed_contacts: 0,
            standing_full_mounts: 0,
            carrier_full_mounts: 0,
            standing_cpu_words: 0,
            standing_device_words: 0,
            carrier_cpu_words: 0,
            carrier_device_words: 0,
            resident_body_key: None,
            resident_revision: None,
            resident_standing: None,
            resident_lineages: BTreeMap::new(),
            staged: None,
            launch_census,
            device,
            max_blocks_per_multiprocessor,
            concurrent_kernels,
            context,
        })
    }
}

impl Drop for CudaLiveCurrentExecutor {
    fn drop(&mut self) {
        // `Drop::drop` runs before the fields are released. Reactivate this owner's context so
        // resident allocations and the module are released under the context which founded them;
        // `context` is deliberately the last field and is destroyed last.
        let _ = self.context.make_current();
    }
}
