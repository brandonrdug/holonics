//! Resident CUDA realization of exact bounded text-section restriction.
//!
//! The conditioned section body remains resident while each query carries only a receiver-bounded
//! aperture and exact interned coordinates. The resident incidence selector returns bounded caused
//! section handles; the following kernel restricts those handles in parallel and returns their
//! masks. The card owns no language role, semantic rank, dominance relation, pair population,
//! source materialization, or generated text.

use core::ffi::c_void;
use std::time::Instant;

use holonic_structure::{LocalSequence, LocalStructureError};
use mount::{
    Context, Device, DeviceBuffer, Dim3, Module, Stream, VirtualDeviceBuffer, VirtualDeviceGrowth,
    SOMA_PTX,
};
use serde::Serialize;
use soma_abi::text_restrict_cuda as wire;

const RESIDENT_LOGICAL_WORD_RESERVATION: usize = u32::MAX as usize;

#[derive(Clone, Debug)]
pub enum TextMaterialCudaError {
    Driver(mount::CudaError),
    EmptyRestriction,
    InvalidWire,
    Extent,
    ResidentMismatch,
    PoisonedRealization,
}

impl TextMaterialCudaError {
    const fn preserves_resident_predecessor(&self) -> bool {
        matches!(
            self,
            Self::EmptyRestriction | Self::InvalidWire | Self::Extent
        )
    }
}

impl From<mount::CudaError> for TextMaterialCudaError {
    fn from(error: mount::CudaError) -> Self {
        Self::Driver(error)
    }
}

impl From<LocalStructureError> for TextMaterialCudaError {
    fn from(_: LocalStructureError) -> Self {
        Self::Extent
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize)]
pub struct TextMaterialResidentShape {
    pub occurrences: usize,
    pub sections: usize,
    pub features: usize,
    pub tokens: usize,
    pub section_feature_words: usize,
    pub section_token_words: usize,
    pub feature_nodes: usize,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize)]
pub struct TextMaterialResidentReservation {
    pub vmm_granularity_bytes: usize,
    pub virtual_reservation_words: usize,
    pub section_row_words: usize,
    pub section_row_mappings: usize,
    pub section_feature_words: usize,
    pub section_feature_mappings: usize,
    pub section_token_words: usize,
    pub section_token_mappings: usize,
    pub feature_heads: usize,
    pub feature_head_mappings: usize,
    pub feature_node_words: usize,
    pub feature_node_mappings: usize,
    pub query_words: usize,
    pub output_words: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct TextMaterialCudaSyncReceipt {
    pub initial_mount: bool,
    pub host_to_device_words: usize,
    pub device_to_host_words: usize,
    pub bounded_delta_equal: bool,
    pub virtual_address_reservations: usize,
    pub newly_mapped_words: usize,
    pub mapping_operations: usize,
    pub transient_allocation_operations: usize,
    pub stable_virtual_bases: bool,
    pub elapsed_nanoseconds: u128,
    pub sync_ordinal: u64,
    pub active: TextMaterialResidentShape,
    pub reserved: TextMaterialResidentReservation,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct TextMaterialCudaLaunchReceipt {
    pub device: String,
    pub handle_aperture: usize,
    pub returned_handles: usize,
    pub restriction_row_words: usize,
    pub query_words: usize,
    pub returned_words: usize,
    pub elapsed_nanoseconds: u128,
    pub prepare_and_ingress_nanoseconds: u128,
    pub kernel_and_stream_nanoseconds: u128,
    pub return_egress_nanoseconds: u128,
    pub launch_ordinal: u64,
    pub query_epoch: u32,
    pub kernel_launches: u32,
    pub transient_allocation_operations: usize,
    pub selector_grid: [u32; 3],
    pub selector_block: [u32; 3],
    pub restriction_grid: [u32; 3],
    pub restriction_block: [u32; 3],
    pub retained_streams: u32,
    pub stream_nonblocking: bool,
    pub stream_synchronizations: u32,
    pub epoch_reset: bool,
    pub active: TextMaterialResidentShape,
    pub reserved: TextMaterialResidentReservation,
}

#[derive(Debug)]
pub(crate) struct TextMaterialResidentImage {
    pub shape: TextMaterialResidentShape,
    pub section_rows: LocalSequence<u32>,
    pub section_features: LocalSequence<u32>,
    pub section_tokens: LocalSequence<u32>,
    pub feature_heads: LocalSequence<u32>,
    pub feature_nodes: LocalSequence<u32>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct TextMaterialFeatureHeadUpdate {
    pub feature: u32,
    pub head: u32,
}

#[derive(Debug)]
pub(crate) struct TextMaterialResidentDelta {
    pub from: TextMaterialResidentShape,
    pub to: TextMaterialResidentShape,
    pub section_rows: LocalSequence<u32>,
    pub section_features: LocalSequence<u32>,
    pub section_tokens: LocalSequence<u32>,
    pub feature_nodes: LocalSequence<u32>,
    pub head_updates: LocalSequence<TextMaterialFeatureHeadUpdate>,
}

pub(crate) struct TextMaterialCudaRestrictionOutput {
    pub restriction_words: LocalSequence<u32>,
    pub returned_handles: usize,
    pub launch: TextMaterialCudaLaunchReceipt,
}

/// One retained CUDA context, resident exact section body, and reusable query apparatus.  Context
/// is last so the module and every allocation disappear before their owning CUDA context.
pub(crate) struct CudaTextMaterialResidentExecutor {
    module: Module,
    device_ordinal: i32,
    device_name: String,
    census: mount::cuda::LaunchCensus,
    launches: u64,
    syncs: u64,
    epoch: u32,
    active: TextMaterialResidentShape,
    head_shadow: LocalSequence<u32>,
    pending_sync: Option<TextMaterialCudaSyncReceipt>,
    poisoned: bool,
    section_rows: VirtualDeviceBuffer<u32>,
    section_features: VirtualDeviceBuffer<u32>,
    section_tokens: VirtualDeviceBuffer<u32>,
    feature_heads: VirtualDeviceBuffer<u32>,
    feature_nodes: VirtualDeviceBuffer<u32>,
    query: DeviceBuffer<u32>,
    output: DeviceBuffer<u32>,
    stream: Stream,
    context: Context,
}

impl std::fmt::Debug for CudaTextMaterialResidentExecutor {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("CudaTextMaterialResidentExecutor")
            .field("device_name", &self.device_name)
            .field("launches", &self.launches)
            .field("syncs", &self.syncs)
            .field("active", &self.active)
            .field("poisoned", &self.poisoned)
            .finish_non_exhaustive()
    }
}

impl CudaTextMaterialResidentExecutor {
    pub(crate) fn mount(
        device_ordinal: i32,
        image: TextMaterialResidentImage,
    ) -> Result<Self, TextMaterialCudaError> {
        validate_image(&image)?;
        mount::cuda::init()?;
        let device = Device::get(device_ordinal)?;
        let census = device.launch_census()?;
        let context = Context::create(&device)?;
        let module = Module::load_ptx(SOMA_PTX)?;
        module.function(wire::SELECT_ENTRY_SYMBOL)?;
        module.function(wire::RESTRICT_ENTRY_SYMBOL)?;

        let sync_started = Instant::now();
        let section_rows = resident_buffer(device_ordinal, &image.section_rows)?;
        let section_features = resident_buffer(device_ordinal, &image.section_features)?;
        let section_tokens = resident_buffer(device_ordinal, &image.section_tokens)?;
        let feature_heads = resident_buffer(device_ordinal, &image.feature_heads)?;
        let feature_nodes = resident_buffer(device_ordinal, &image.feature_nodes)?;
        let query = DeviceBuffer::<u32>::alloc_zeroed(1)?;
        let output = DeviceBuffer::<u32>::alloc_zeroed(1)?;
        let stream = Stream::create()?;
        context.synchronize()?;
        let device_to_host_words = verify_resident_image(
            &section_rows,
            &section_features,
            &section_tokens,
            &feature_heads,
            &feature_nodes,
            &image,
        )?;
        let host_to_device_words = image
            .section_rows
            .len()
            .checked_add(image.section_features.len())
            .and_then(|words| words.checked_add(image.section_tokens.len()))
            .and_then(|words| words.checked_add(image.feature_heads.len()))
            .and_then(|words| words.checked_add(image.feature_nodes.len()))
            .ok_or(TextMaterialCudaError::Extent)?;
        let active = image.shape;
        let head_shadow = image.feature_heads;
        let newly_mapped_words = section_rows
            .mapped_elements()
            .checked_add(section_features.mapped_elements())
            .and_then(|words| words.checked_add(section_tokens.mapped_elements()))
            .and_then(|words| words.checked_add(feature_heads.mapped_elements()))
            .and_then(|words| words.checked_add(feature_nodes.mapped_elements()))
            .ok_or(TextMaterialCudaError::Extent)?;
        let mapping_operations = section_rows
            .mapping_count()
            .checked_add(section_features.mapping_count())
            .and_then(|count| count.checked_add(section_tokens.mapping_count()))
            .and_then(|count| count.checked_add(feature_heads.mapping_count()))
            .and_then(|count| count.checked_add(feature_nodes.mapping_count()))
            .ok_or(TextMaterialCudaError::Extent)?;
        let reserved = TextMaterialResidentReservation {
            vmm_granularity_bytes: section_rows.granularity_bytes(),
            virtual_reservation_words: section_rows.logical_reservation_elements(),
            section_row_words: section_rows.mapped_elements(),
            section_row_mappings: section_rows.mapping_count(),
            section_feature_words: section_features.mapped_elements(),
            section_feature_mappings: section_features.mapping_count(),
            section_token_words: section_tokens.mapped_elements(),
            section_token_mappings: section_tokens.mapping_count(),
            feature_heads: feature_heads.mapped_elements(),
            feature_head_mappings: feature_heads.mapping_count(),
            feature_node_words: feature_nodes.mapped_elements(),
            feature_node_mappings: feature_nodes.mapping_count(),
            query_words: query.len(),
            output_words: output.len(),
        };
        let pending_sync = Some(TextMaterialCudaSyncReceipt {
            initial_mount: true,
            host_to_device_words,
            device_to_host_words,
            bounded_delta_equal: true,
            virtual_address_reservations: 5,
            newly_mapped_words,
            mapping_operations,
            transient_allocation_operations: 2,
            stable_virtual_bases: true,
            elapsed_nanoseconds: sync_started.elapsed().as_nanos(),
            sync_ordinal: 1,
            active,
            reserved,
        });
        Ok(Self {
            module,
            device_ordinal,
            device_name: device.name,
            census,
            launches: 0,
            syncs: 1,
            epoch: 0,
            active,
            head_shadow,
            pending_sync,
            poisoned: false,
            section_rows,
            section_features,
            section_tokens,
            feature_heads,
            feature_nodes,
            query,
            output,
            stream,
            context,
        })
    }

    pub(crate) const fn device_ordinal(&self) -> i32 {
        self.device_ordinal
    }

    pub(crate) fn device_name(&self) -> &str {
        &self.device_name
    }

    pub(crate) const fn launches(&self) -> u64 {
        self.launches
    }

    pub(crate) const fn active_shape(&self) -> TextMaterialResidentShape {
        self.active
    }

    pub(crate) fn head_shadow(&self) -> &[u32] {
        &self.head_shadow
    }

    pub(crate) const fn is_poisoned(&self) -> bool {
        self.poisoned
    }

    pub(crate) fn take_pending_sync(&mut self) -> Option<TextMaterialCudaSyncReceipt> {
        self.pending_sync.take()
    }

    pub(crate) fn synchronize(
        &mut self,
        delta: TextMaterialResidentDelta,
    ) -> Result<(), TextMaterialCudaError> {
        if self.poisoned {
            return Err(TextMaterialCudaError::PoisonedRealization);
        }
        match self.synchronize_inner(delta) {
            Ok(()) => Ok(()),
            Err(error) => {
                self.poisoned = true;
                Err(error)
            }
        }
    }

    fn synchronize_inner(
        &mut self,
        delta: TextMaterialResidentDelta,
    ) -> Result<(), TextMaterialCudaError> {
        validate_delta(self.active, &delta, &self.head_shadow)?;
        self.context.make_current()?;
        let sync_started = Instant::now();
        let bases_before = [
            self.section_rows.base_address(),
            self.section_features.base_address(),
            self.section_tokens.base_address(),
            self.feature_heads.base_address(),
            self.feature_nodes.base_address(),
        ];
        let row_growth = self.section_rows.ensure_mapped(
            delta
                .to
                .sections
                .checked_mul(wire::SECTION_ROW_WORDS)
                .ok_or(TextMaterialCudaError::Extent)?,
        )?;
        let feature_growth = self
            .section_features
            .ensure_mapped(delta.to.section_feature_words)?;
        let token_growth = self
            .section_tokens
            .ensure_mapped(delta.to.section_token_words)?;
        let head_growth = self.feature_heads.ensure_mapped(delta.to.features)?;
        let node_growth = self.feature_nodes.ensure_mapped(
            delta
                .to
                .feature_nodes
                .checked_mul(wire::FEATURE_NODE_WORDS)
                .ok_or(TextMaterialCudaError::Extent)?,
        )?;
        let newly_mapped_words = growth_elements([
            row_growth,
            feature_growth,
            token_growth,
            head_growth,
            node_growth,
        ])?;
        let mapping_operations = growth_operations([
            row_growth,
            feature_growth,
            token_growth,
            head_growth,
            node_growth,
        ])?;
        let bases_after = [
            self.section_rows.base_address(),
            self.section_features.base_address(),
            self.section_tokens.base_address(),
            self.feature_heads.base_address(),
            self.feature_nodes.base_address(),
        ];
        let stable_virtual_bases = bases_before == bases_after
            && row_growth.base_address_unchanged
            && feature_growth.base_address_unchanged
            && token_growth.base_address_unchanged
            && head_growth.base_address_unchanged
            && node_growth.base_address_unchanged;
        let transient_allocation_operations = 0usize;
        self.section_rows.copy_range_from_slice(
            delta.from.sections * wire::SECTION_ROW_WORDS,
            &delta.section_rows,
        )?;
        self.section_features
            .copy_range_from_slice(delta.from.section_feature_words, &delta.section_features)?;
        self.section_tokens
            .copy_range_from_slice(delta.from.section_token_words, &delta.section_tokens)?;
        self.feature_nodes.copy_range_from_slice(
            delta.from.feature_nodes * wire::FEATURE_NODE_WORDS,
            &delta.feature_nodes,
        )?;
        let new_features = delta.to.features - delta.from.features;
        let mut open_heads = LocalSequence::with_capacity(new_features);
        open_heads.resize_with(new_features, || wire::OPEN_LINK);
        self.feature_heads
            .copy_range_from_slice(delta.from.features, &open_heads)?;

        // Head publication is the final physical commit.  Every node and every section body it
        // exposes is already resident before any existing feature can reach the appended suffix.
        for update in &delta.head_updates {
            self.feature_heads.copy_range_from_slice(
                usize::try_from(update.feature).map_err(|_| TextMaterialCudaError::Extent)?,
                &[update.head],
            )?;
        }
        self.context.synchronize()?;

        let device_to_host_words = self.verify_resident_delta(&delta)?;

        self.head_shadow
            .resize_with(delta.to.features, || wire::OPEN_LINK);
        for update in &delta.head_updates {
            let head = self
                .head_shadow
                .get_mut(
                    usize::try_from(update.feature).map_err(|_| TextMaterialCudaError::Extent)?,
                )
                .ok_or(TextMaterialCudaError::ResidentMismatch)?;
            *head = update.head;
        }
        self.active = delta.to;
        self.syncs = self
            .syncs
            .checked_add(1)
            .ok_or(TextMaterialCudaError::Extent)?;
        let host_to_device_words = delta
            .section_rows
            .len()
            .checked_add(delta.section_features.len())
            .and_then(|words| words.checked_add(delta.section_tokens.len()))
            .and_then(|words| words.checked_add(delta.feature_nodes.len()))
            .and_then(|words| words.checked_add(new_features))
            .and_then(|words| words.checked_add(delta.head_updates.len()))
            .ok_or(TextMaterialCudaError::Extent)?;
        self.pending_sync = Some(TextMaterialCudaSyncReceipt {
            initial_mount: false,
            host_to_device_words,
            device_to_host_words,
            bounded_delta_equal: true,
            virtual_address_reservations: 0,
            newly_mapped_words,
            mapping_operations,
            transient_allocation_operations,
            stable_virtual_bases,
            elapsed_nanoseconds: sync_started.elapsed().as_nanos(),
            sync_ordinal: self.syncs,
            active: self.active,
            reserved: self.reservation(),
        });
        Ok(())
    }

    /// Read back only the changed resident suffix and changed head cells. This is the bounded
    /// physical equality witness for an append delta; it never replays a restriction or copies
    /// the complete standing body.
    fn verify_resident_delta(
        &self,
        delta: &TextMaterialResidentDelta,
    ) -> Result<usize, TextMaterialCudaError> {
        let mut verified_words = 0usize;
        let mut section_rows = LocalSequence::with_capacity(delta.section_rows.len());
        section_rows.resize_with(delta.section_rows.len(), || 0);
        self.section_rows.copy_range_to_slice(
            delta.from.sections * wire::SECTION_ROW_WORDS,
            &mut section_rows,
        )?;
        if section_rows != delta.section_rows {
            return Err(TextMaterialCudaError::ResidentMismatch);
        }
        verified_words = verified_words
            .checked_add(section_rows.len())
            .ok_or(TextMaterialCudaError::Extent)?;

        let mut section_features = LocalSequence::with_capacity(delta.section_features.len());
        section_features.resize_with(delta.section_features.len(), || 0);
        self.section_features
            .copy_range_to_slice(delta.from.section_feature_words, &mut section_features)?;
        if section_features != delta.section_features {
            return Err(TextMaterialCudaError::ResidentMismatch);
        }
        verified_words = verified_words
            .checked_add(section_features.len())
            .ok_or(TextMaterialCudaError::Extent)?;

        let mut section_tokens = LocalSequence::with_capacity(delta.section_tokens.len());
        section_tokens.resize_with(delta.section_tokens.len(), || 0);
        self.section_tokens
            .copy_range_to_slice(delta.from.section_token_words, &mut section_tokens)?;
        if section_tokens != delta.section_tokens {
            return Err(TextMaterialCudaError::ResidentMismatch);
        }
        verified_words = verified_words
            .checked_add(section_tokens.len())
            .ok_or(TextMaterialCudaError::Extent)?;

        let mut feature_nodes = LocalSequence::with_capacity(delta.feature_nodes.len());
        feature_nodes.resize_with(delta.feature_nodes.len(), || 0);
        self.feature_nodes.copy_range_to_slice(
            delta.from.feature_nodes * wire::FEATURE_NODE_WORDS,
            &mut feature_nodes,
        )?;
        if feature_nodes != delta.feature_nodes {
            return Err(TextMaterialCudaError::ResidentMismatch);
        }
        verified_words = verified_words
            .checked_add(feature_nodes.len())
            .ok_or(TextMaterialCudaError::Extent)?;

        let appended_features = delta.to.features - delta.from.features;
        let mut expected_heads = LocalSequence::with_capacity(appended_features);
        expected_heads.resize_with(appended_features, || wire::OPEN_LINK);
        for update in &delta.head_updates {
            let feature =
                usize::try_from(update.feature).map_err(|_| TextMaterialCudaError::Extent)?;
            if feature >= delta.from.features {
                expected_heads[feature - delta.from.features] = update.head;
            }
        }
        let mut returned_heads = LocalSequence::with_capacity(appended_features);
        returned_heads.resize_with(appended_features, || wire::OPEN_LINK);
        self.feature_heads
            .copy_range_to_slice(delta.from.features, &mut returned_heads)?;
        if returned_heads != expected_heads {
            return Err(TextMaterialCudaError::ResidentMismatch);
        }
        verified_words = verified_words
            .checked_add(returned_heads.len())
            .ok_or(TextMaterialCudaError::Extent)?;
        for update in &delta.head_updates {
            let feature =
                usize::try_from(update.feature).map_err(|_| TextMaterialCudaError::Extent)?;
            if feature >= delta.from.features {
                continue;
            }
            let mut returned = [wire::OPEN_LINK];
            self.feature_heads
                .copy_range_to_slice(feature, &mut returned)?;
            if returned[0] != update.head {
                return Err(TextMaterialCudaError::ResidentMismatch);
            }
            verified_words = verified_words
                .checked_add(1)
                .ok_or(TextMaterialCudaError::Extent)?;
        }
        Ok(verified_words)
    }

    pub(crate) fn restrict(
        &mut self,
        query_words: &mut [u32],
    ) -> Result<TextMaterialCudaRestrictionOutput, TextMaterialCudaError> {
        if self.poisoned {
            return Err(TextMaterialCudaError::PoisonedRealization);
        }
        match self.restrict_inner(query_words) {
            Ok(output) => Ok(output),
            Err(error) => {
                if !error.preserves_resident_predecessor() {
                    self.poisoned = true;
                }
                Err(error)
            }
        }
    }

    fn restrict_inner(
        &mut self,
        query_words: &mut [u32],
    ) -> Result<TextMaterialCudaRestrictionOutput, TextMaterialCudaError> {
        validate_query(query_words)?;
        let aperture = usize::try_from(query_words[wire::APERTURE])
            .map_err(|_| TextMaterialCudaError::Extent)?;
        if aperture == 0 || self.active.sections == 0 || aperture > self.active.sections {
            return Err(TextMaterialCudaError::EmptyRestriction);
        }

        self.context.make_current()?;
        let started = Instant::now();
        let epoch_reset = if self.epoch == u32::MAX {
            self.epoch = 1;
            true
        } else {
            self.epoch += 1;
            false
        };
        query_words[wire::EPOCH] = self.epoch;
        let mut transient_allocation_operations =
            usize::from(grow_transient(&mut self.query, query_words.len())?);
        self.query.copy_range_from_slice(0, query_words)?;

        let feature_mask_words = usize::try_from(query_words[wire::FEATURE_MASK_WORDS])
            .map_err(|_| TextMaterialCudaError::Extent)?;
        let transport_mask_words = usize::try_from(query_words[wire::TRANSPORT_MASK_WORDS])
            .map_err(|_| TextMaterialCudaError::Extent)?;
        let row_words = feature_mask_words
            .checked_add(transport_mask_words)
            .and_then(|words| words.checked_add(wire::RETURN_MASK_AT))
            .ok_or(TextMaterialCudaError::Extent)?;
        let output_words = aperture
            .checked_mul(row_words)
            .and_then(|words| words.checked_add(wire::RETURN_HEADER_WORDS))
            .ok_or(TextMaterialCudaError::Extent)?;
        transient_allocation_operations +=
            usize::from(grow_transient(&mut self.output, output_words)?);

        let selector = self.module.function(wire::SELECT_ENTRY_SYMBOL)?;
        let function = self.module.function(wire::RESTRICT_ENTRY_SYMBOL)?;
        let launch = function.linear_launch(
            self.census,
            u64::try_from(aperture).map_err(|_| TextMaterialCudaError::Extent)?,
        )?;
        let mut query_pointer = self.query.device_ptr();
        let mut query_extent =
            u64::try_from(query_words.len()).map_err(|_| TextMaterialCudaError::Extent)?;
        let mut rows_pointer = self.section_rows.device_ptr();
        let mut rows_extent = u64::try_from(self.active.sections * wire::SECTION_ROW_WORDS)
            .map_err(|_| TextMaterialCudaError::Extent)?;
        let mut section_features_pointer = self.section_features.device_ptr();
        let mut section_features_extent = u64::try_from(self.active.section_feature_words)
            .map_err(|_| TextMaterialCudaError::Extent)?;
        let mut tokens_pointer = self.section_tokens.device_ptr();
        let mut tokens_extent = u64::try_from(self.active.section_token_words)
            .map_err(|_| TextMaterialCudaError::Extent)?;
        let mut feature_heads_pointer = self.feature_heads.device_ptr();
        let mut feature_heads_extent =
            u64::try_from(self.active.features).map_err(|_| TextMaterialCudaError::Extent)?;
        let mut feature_nodes_pointer = self.feature_nodes.device_ptr();
        let mut feature_nodes_extent = u64::try_from(
            self.active
                .feature_nodes
                .checked_mul(wire::FEATURE_NODE_WORDS)
                .ok_or(TextMaterialCudaError::Extent)?,
        )
        .map_err(|_| TextMaterialCudaError::Extent)?;
        let mut output_pointer = self.output.device_ptr();
        let mut output_extent =
            u64::try_from(output_words).map_err(|_| TextMaterialCudaError::Extent)?;
        let mut active_sections =
            u32::try_from(self.active.sections).map_err(|_| TextMaterialCudaError::Extent)?;
        let mut active_features =
            u32::try_from(self.active.features).map_err(|_| TextMaterialCudaError::Extent)?;
        let mut stride = launch.x_stride;
        let mut selector_params = [
            &mut query_pointer as *mut u64 as *mut c_void,
            &mut query_extent as *mut u64 as *mut c_void,
            &mut feature_heads_pointer as *mut u64 as *mut c_void,
            &mut feature_heads_extent as *mut u64 as *mut c_void,
            &mut feature_nodes_pointer as *mut u64 as *mut c_void,
            &mut feature_nodes_extent as *mut u64 as *mut c_void,
            &mut output_pointer as *mut u64 as *mut c_void,
            &mut output_extent as *mut u64 as *mut c_void,
            &mut active_sections as *mut u32 as *mut c_void,
            &mut active_features as *mut u32 as *mut c_void,
        ];
        let mut restriction_params = [
            &mut query_pointer as *mut u64 as *mut c_void,
            &mut query_extent as *mut u64 as *mut c_void,
            &mut rows_pointer as *mut u64 as *mut c_void,
            &mut rows_extent as *mut u64 as *mut c_void,
            &mut section_features_pointer as *mut u64 as *mut c_void,
            &mut section_features_extent as *mut u64 as *mut c_void,
            &mut tokens_pointer as *mut u64 as *mut c_void,
            &mut tokens_extent as *mut u64 as *mut c_void,
            &mut output_pointer as *mut u64 as *mut c_void,
            &mut output_extent as *mut u64 as *mut c_void,
            &mut active_sections as *mut u32 as *mut c_void,
            &mut stride as *mut u32 as *mut c_void,
        ];
        let prepare_and_ingress_nanoseconds = started.elapsed().as_nanos();
        let kernel_started = Instant::now();
        selector.launch_on(&self.stream, Dim3::x(1), Dim3::x(1), &mut selector_params)?;
        function.launch_on(
            &self.stream,
            launch.grid,
            launch.block,
            &mut restriction_params,
        )?;
        self.stream.synchronize()?;
        let kernel_and_stream_nanoseconds = kernel_started.elapsed().as_nanos();

        let egress_started = Instant::now();
        let mut restriction_words = LocalSequence::with_capacity(output_words);
        restriction_words.resize_with(output_words, || 0);
        self.output.copy_range_to_slice(0, &mut restriction_words)?;
        let complete_population =
            usize::try_from(restriction_words[wire::RETURN_COMPLETE_POPULATION])
                .map_err(|_| TextMaterialCudaError::Extent)?;
        let returned_handles = usize::try_from(restriction_words[wire::RETURN_HANDLE_POPULATION])
            .map_err(|_| TextMaterialCudaError::Extent)?;
        if returned_handles > aperture || complete_population < returned_handles {
            return Err(TextMaterialCudaError::ResidentMismatch);
        }
        let return_egress_nanoseconds = egress_started.elapsed().as_nanos();
        self.launches = self
            .launches
            .checked_add(1)
            .ok_or(TextMaterialCudaError::Extent)?;
        let receipt = TextMaterialCudaLaunchReceipt {
            device: self.device_name.to_owned(),
            handle_aperture: aperture,
            returned_handles,
            restriction_row_words: row_words,
            query_words: query_words.len(),
            returned_words: output_words,
            elapsed_nanoseconds: started.elapsed().as_nanos(),
            prepare_and_ingress_nanoseconds,
            kernel_and_stream_nanoseconds,
            return_egress_nanoseconds,
            launch_ordinal: self.launches,
            query_epoch: self.epoch,
            kernel_launches: 2,
            transient_allocation_operations,
            selector_grid: [1, 1, 1],
            selector_block: [1, 1, 1],
            restriction_grid: dim_words(launch.grid),
            restriction_block: dim_words(launch.block),
            retained_streams: 1,
            stream_nonblocking: self.stream.is_nonblocking(),
            stream_synchronizations: 1,
            epoch_reset,
            active: self.active,
            reserved: self.reservation(),
        };
        Ok(TextMaterialCudaRestrictionOutput {
            restriction_words,
            returned_handles,
            launch: receipt,
        })
    }

    fn reservation(&self) -> TextMaterialResidentReservation {
        TextMaterialResidentReservation {
            vmm_granularity_bytes: self.section_rows.granularity_bytes(),
            virtual_reservation_words: self.section_rows.logical_reservation_elements(),
            section_row_words: self.section_rows.mapped_elements(),
            section_row_mappings: self.section_rows.mapping_count(),
            section_feature_words: self.section_features.mapped_elements(),
            section_feature_mappings: self.section_features.mapping_count(),
            section_token_words: self.section_tokens.mapped_elements(),
            section_token_mappings: self.section_tokens.mapping_count(),
            feature_heads: self.feature_heads.mapped_elements(),
            feature_head_mappings: self.feature_heads.mapping_count(),
            feature_node_words: self.feature_nodes.mapped_elements(),
            feature_node_mappings: self.feature_nodes.mapping_count(),
            query_words: self.query.len(),
            output_words: self.output.len(),
        }
    }
}

impl Drop for CudaTextMaterialResidentExecutor {
    fn drop(&mut self) {
        // The retained device arrays and module belong to this executor's context. `drop` runs
        // before fields are released; restoring the apparatus chart here makes every subsequent
        // field teardown occur under the context that founded it. `context` is deliberately last.
        let _ = self.context.make_current();
    }
}

fn resident_buffer(
    device_ordinal: i32,
    words: &[u32],
) -> Result<VirtualDeviceBuffer<u32>, TextMaterialCudaError> {
    let buffer = VirtualDeviceBuffer::<u32>::reserve(
        device_ordinal,
        RESIDENT_LOGICAL_WORD_RESERVATION,
        words.len(),
    )?;
    buffer.copy_range_from_slice(0, words)?;
    Ok(buffer)
}

fn verify_resident_image(
    section_rows: &VirtualDeviceBuffer<u32>,
    section_features: &VirtualDeviceBuffer<u32>,
    section_tokens: &VirtualDeviceBuffer<u32>,
    feature_heads: &VirtualDeviceBuffer<u32>,
    feature_nodes: &VirtualDeviceBuffer<u32>,
    image: &TextMaterialResidentImage,
) -> Result<usize, TextMaterialCudaError> {
    let mut verified = 0usize;
    for (resident, expected) in [
        (section_rows, image.section_rows.as_ref()),
        (section_features, image.section_features.as_ref()),
        (section_tokens, image.section_tokens.as_ref()),
        (feature_heads, image.feature_heads.as_ref()),
        (feature_nodes, image.feature_nodes.as_ref()),
    ] {
        let mut returned = LocalSequence::with_capacity(expected.len());
        returned.resize_with(expected.len(), || 0);
        resident.copy_range_to_slice(0, &mut returned)?;
        if returned.as_ref() != expected {
            return Err(TextMaterialCudaError::ResidentMismatch);
        }
        verified = verified
            .checked_add(returned.len())
            .ok_or(TextMaterialCudaError::Extent)?;
    }
    Ok(verified)
}

fn growth_elements(growth: [VirtualDeviceGrowth; 5]) -> Result<usize, TextMaterialCudaError> {
    let mut total = 0usize;
    for receipt in growth {
        total = total
            .checked_add(receipt.newly_mapped_elements)
            .ok_or(TextMaterialCudaError::Extent)?;
    }
    Ok(total)
}

fn growth_operations(growth: [VirtualDeviceGrowth; 5]) -> Result<usize, TextMaterialCudaError> {
    let mut total = 0usize;
    for receipt in growth {
        total = total
            .checked_add(receipt.mapping_operations)
            .ok_or(TextMaterialCudaError::Extent)?;
    }
    Ok(total)
}

fn grown_extent(current: usize, required: usize) -> Result<usize, TextMaterialCudaError> {
    if required <= current {
        return Ok(current);
    }
    if current == 0 {
        return Ok(required.max(1));
    }
    let margin = (current / 16).max(required - current).max(64);
    current
        .checked_add(margin)
        .map(|grown| grown.max(required))
        .ok_or(TextMaterialCudaError::Extent)
}

fn grow_transient(
    buffer: &mut DeviceBuffer<u32>,
    required: usize,
) -> Result<bool, TextMaterialCudaError> {
    if required <= buffer.len() {
        return Ok(false);
    }
    *buffer = DeviceBuffer::<u32>::alloc_zeroed(grown_extent(buffer.len(), required)?)?;
    Ok(true)
}

fn validate_image(image: &TextMaterialResidentImage) -> Result<(), TextMaterialCudaError> {
    let shape = image.shape;
    if image.section_rows.len()
        != shape
            .sections
            .checked_mul(wire::SECTION_ROW_WORDS)
            .ok_or(TextMaterialCudaError::Extent)?
        || image.section_features.len() != shape.section_feature_words
        || image.section_tokens.len() != shape.section_token_words
        || image.feature_heads.len() != shape.features
        || image.feature_nodes.len()
            != shape
                .feature_nodes
                .checked_mul(wire::FEATURE_NODE_WORDS)
                .ok_or(TextMaterialCudaError::Extent)?
        || shape.feature_nodes != shape.section_feature_words
    {
        return Err(TextMaterialCudaError::ResidentMismatch);
    }
    Ok(())
}

fn validate_delta(
    active: TextMaterialResidentShape,
    delta: &TextMaterialResidentDelta,
    heads: &[u32],
) -> Result<(), TextMaterialCudaError> {
    if active != delta.from
        || delta.to.occurrences < delta.from.occurrences
        || delta.to.sections < delta.from.sections
        || delta.to.features < delta.from.features
        || delta.to.tokens < delta.from.tokens
        || delta.to.section_feature_words < delta.from.section_feature_words
        || delta.to.section_token_words < delta.from.section_token_words
        || delta.to.feature_nodes < delta.from.feature_nodes
        || heads.len() != delta.from.features
        || delta.to.feature_nodes != delta.to.section_feature_words
        || delta.section_rows.len()
            != (delta.to.sections - delta.from.sections)
                .checked_mul(wire::SECTION_ROW_WORDS)
                .ok_or(TextMaterialCudaError::Extent)?
        || delta.section_features.len()
            != delta.to.section_feature_words - delta.from.section_feature_words
        || delta.section_tokens.len()
            != delta.to.section_token_words - delta.from.section_token_words
        || delta.feature_nodes.len()
            != (delta.to.feature_nodes - delta.from.feature_nodes)
                .checked_mul(wire::FEATURE_NODE_WORDS)
                .ok_or(TextMaterialCudaError::Extent)?
    {
        return Err(TextMaterialCudaError::ResidentMismatch);
    }
    for update in &delta.head_updates {
        if usize::try_from(update.feature).map_err(|_| TextMaterialCudaError::Extent)?
            >= delta.to.features
            || usize::try_from(update.head).map_err(|_| TextMaterialCudaError::Extent)?
                >= delta.to.feature_nodes
        {
            return Err(TextMaterialCudaError::ResidentMismatch);
        }
    }
    Ok(())
}

fn validate_query(query: &[u32]) -> Result<(), TextMaterialCudaError> {
    if query.len() < wire::HEADER_WORDS
        || query[wire::VERSION] != wire::LAYOUT_VERSION
        || usize::try_from(query[wire::TOTAL_WORDS]).ok() != Some(query.len())
        || usize::try_from(query[wire::FEATURE_MASK_WORDS]).ok()
            != Some(wire::mask_words(
                usize::try_from(query[wire::LEADER_FEATURES])
                    .map_err(|_| TextMaterialCudaError::Extent)?,
            ))
        || usize::try_from(query[wire::TRANSPORT_MASK_WORDS]).ok()
            != Some(wire::mask_words(
                usize::try_from(query[wire::QUERY_TRANSPORTS])
                    .map_err(|_| TextMaterialCudaError::Extent)?,
            ))
    {
        return Err(TextMaterialCudaError::InvalidWire);
    }
    let aperture =
        usize::try_from(query[wire::APERTURE]).map_err(|_| TextMaterialCudaError::Extent)?;
    let features_at = usize::try_from(query[wire::LEADER_FEATURES_AT])
        .map_err(|_| TextMaterialCudaError::Extent)?;
    let transports_at = usize::try_from(query[wire::QUERY_TRANSPORTS_AT])
        .map_err(|_| TextMaterialCudaError::Extent)?;
    let cursors_at = usize::try_from(query[wire::FEATURE_CURSORS_AT])
        .map_err(|_| TextMaterialCudaError::Extent)?;
    let features =
        usize::try_from(query[wire::LEADER_FEATURES]).map_err(|_| TextMaterialCudaError::Extent)?;
    let transports = usize::try_from(query[wire::QUERY_TRANSPORTS])
        .map_err(|_| TextMaterialCudaError::Extent)?;
    if aperture == 0
        || features == 0
        || features_at != wire::HEADER_WORDS
        || transports_at
            != features_at
                .checked_add(features)
                .ok_or(TextMaterialCudaError::Extent)?
        || cursors_at
            != transports_at
                .checked_add(
                    transports
                        .checked_mul(wire::TRANSPORT_WORDS)
                        .ok_or(TextMaterialCudaError::Extent)?,
                )
                .ok_or(TextMaterialCudaError::Extent)?
        || query.len()
            != cursors_at
                .checked_add(features)
                .ok_or(TextMaterialCudaError::Extent)?
    {
        return Err(TextMaterialCudaError::InvalidWire);
    }
    Ok(())
}

fn dim_words(dim: mount::Dim3) -> [u32; 3] {
    [dim.x, dim.y, dim.z]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn query_wire_has_only_aperture_coordinates_and_cursor_scratch() {
        let features = [3u32, 8];
        let transports = [(13u32, 21u32)];
        let words = wire::HEADER_WORDS
            + features.len()
            + transports.len() * wire::TRANSPORT_WORDS
            + features.len();
        let mut query = LocalSequence::with_capacity(words);
        query.resize_with(wire::HEADER_WORDS, || 0);
        let features_at = query.len();
        query.extend_from_slice(&features);
        let transports_at = query.len();
        query.extend_from_slice(&[transports[0].0, transports[0].1]);
        let cursors_at = query.len();
        query.resize_with(words, || wire::OPEN_LINK);
        query[wire::VERSION] = wire::LAYOUT_VERSION;
        query[wire::APERTURE] = 2;
        query[wire::LEADER_FEATURES] = features.len() as u32;
        query[wire::QUERY_TRANSPORTS] = transports.len() as u32;
        query[wire::FEATURE_MASK_WORDS] = wire::mask_words(features.len()) as u32;
        query[wire::TRANSPORT_MASK_WORDS] = wire::mask_words(transports.len()) as u32;
        query[wire::LEADER_FEATURES_AT] = features_at as u32;
        query[wire::QUERY_TRANSPORTS_AT] = transports_at as u32;
        query[wire::FEATURE_CURSORS_AT] = cursors_at as u32;
        query[wire::TOTAL_WORDS] = words as u32;
        assert!(validate_query(&query).is_ok());

        query[wire::VERSION] = wire::LAYOUT_VERSION - 1;
        assert!(matches!(
            validate_query(&query),
            Err(TextMaterialCudaError::InvalidWire)
        ));
    }
}
