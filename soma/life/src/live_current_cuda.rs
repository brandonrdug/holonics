//! Resident CUDA execution owner for the live-current membrane.
//!
//! One context and one module remain mounted. One parallel contact launch per receiving current
//! forms its immutable standing-before field; one lineage launch then changes that current's sole
//! mutable carrier. Reusable physical apertures grow after actual pressure and retry from the
//! unchanged predecessor. No active cut, dataset, journal, receipt, or ancestry population is
//! allocated on the card.

use std::collections::BTreeMap;

use ::mount::{
    Context, Device, DeviceBuffer, LiveEventArguments, LiveEventSpan, Module,
    RegionalContactArguments, SOMA_PTX,
};
use body::manifold::{
    node_packed_word, LiveBodyHeader, SparseOwnCell, CARRIER_HEADER_WORDS, ENCLOSURE_WORDS,
    NODE_WORDS,
};
use body::medium::FORM_WORDS;
use body::num::COG_WORDS;
use soma_abi::emission::{DeedEmission, DEED_WORDS};
use soma_abi::live_event_cuda as cuda;
use soma_membrane::{
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
    module: Module,
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
    standing_host_words: u64,
    standing_device_words: u64,
    carrier_host_words: u64,
    carrier_device_words: u64,
    resident_body_key: Option<usize>,
    resident_revision: Option<u64>,
    resident_standing: Option<ResidentStanding>,
    resident_lineages: BTreeMap<CurrentLineage, ResidentCarrier>,
    staged: Option<StagedEvent>,
    context: Context,
}

impl CudaLiveCurrentExecutor {
    pub fn new(device_ordinal: i32) -> ::mount::Result<Self> {
        ::mount::cuda::init()?;
        let device = Device::get(device_ordinal)?;
        let context = Context::create(&device)?;
        let module = Module::load_ptx(SOMA_PTX)?;
        let local = module.lineage_event()?.local_size_bytes()?;
        let stack = local
            .max(LIVE_EVENT_STACK_MIN_BYTES)
            .checked_next_power_of_two()
            .ok_or_else(|| ::mount::CudaError {
                code: -1,
                name: String::from("LIVE_EVENT_STACK_EXTENT"),
                message: String::from("lineage_event local-memory extent cannot be rounded"),
                context: "CudaLiveCurrentExecutor::new",
            })?;
        let stack_limit_bytes = context.ensure_stack_limit_bytes(stack)?;
        Ok(Self {
            module,
            device_name: device.name,
            stack_limit_bytes,
            stack_growths: 0,
            launches: 0,
            contact_launches: 0,
            parallel_contact_lanes: 0,
            resource_retries: 0,
            directed_contacts: 0,
            standing_full_mounts: 0,
            carrier_full_mounts: 0,
            standing_host_words: 0,
            standing_device_words: 0,
            carrier_host_words: 0,
            carrier_device_words: 0,
            resident_body_key: None,
            resident_revision: None,
            resident_standing: None,
            resident_lineages: BTreeMap::new(),
            staged: None,
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
