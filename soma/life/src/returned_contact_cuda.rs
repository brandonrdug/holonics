//! CUDA-owned grouping of exact returned-contact movements.
//!
//! The semantic owner keeps the target and occurrence atlases.  This apparatus receives only their
//! dense integer addresses plus the exact local before/after relation rows.  The card validates the
//! exclusive movement, groups all causes by target, and independently disposes every occurrence.
//! Only those already-grouped rows return; the sparse relation population and its grouping never
//! cross back to the host.

use core::ffi::c_void;
use std::time::Instant;

use holonic_structure::{LocalSequence, LocalStructureError};
use mount::{Context, Device, DeviceBuffer, Module, Stream, SOMA_PTX};
use serde::Serialize;

use soma_abi::returned_contact_cuda as wire;
pub use soma_abi::returned_contact_cuda::ReturnedContactRelation;

#[derive(Clone, Debug)]
pub enum ReturnedContactCudaError {
    Driver(mount::CudaError),
    Extent,
    InvalidFront,
    DeviceRefused { relation: Option<u32> },
    InvalidDeviceReturn,
    PoisonedRealization,
}

impl ReturnedContactCudaError {
    const fn poisons_realization(&self) -> bool {
        matches!(self, Self::Driver(_) | Self::InvalidDeviceReturn)
    }
}

impl std::fmt::Display for ReturnedContactCudaError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Driver(error) => write!(formatter, "{error}"),
            Self::Extent => write!(
                formatter,
                "a returned-contact extent exceeded its exact wire"
            ),
            Self::InvalidFront => write!(formatter, "the returned-contact front is malformed"),
            Self::DeviceRefused {
                relation: Some(relation),
            } => write!(
                formatter,
                "the card refused returned-contact relation {relation}"
            ),
            Self::DeviceRefused { relation: None } => {
                write!(
                    formatter,
                    "the card refused the returned-contact population"
                )
            }
            Self::InvalidDeviceReturn => {
                write!(
                    formatter,
                    "the card returned a malformed returned-contact grouping"
                )
            }
            Self::PoisonedRealization => {
                write!(
                    formatter,
                    "the returned-contact CUDA realization is poisoned"
                )
            }
        }
    }
}

impl std::error::Error for ReturnedContactCudaError {}

impl From<mount::CudaError> for ReturnedContactCudaError {
    fn from(error: mount::CudaError) -> Self {
        Self::Driver(error)
    }
}

impl From<LocalStructureError> for ReturnedContactCudaError {
    fn from(_: LocalStructureError) -> Self {
        Self::Extent
    }
}

/// One sparse integer relation sheet.  The caller retains the exact target and occurrence atlases
/// whose dense addresses these rows carry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReturnedContactCudaFront {
    targets: usize,
    occurrences: usize,
    relations: LocalSequence<ReturnedContactRelation>,
}

impl ReturnedContactCudaFront {
    pub fn new(
        targets: usize,
        occurrences: usize,
        relations: LocalSequence<ReturnedContactRelation>,
    ) -> Result<Self, ReturnedContactCudaError> {
        u32::try_from(targets).map_err(|_| ReturnedContactCudaError::Extent)?;
        u32::try_from(occurrences).map_err(|_| ReturnedContactCudaError::Extent)?;
        u32::try_from(relations.len()).map_err(|_| ReturnedContactCudaError::Extent)?;
        for relation in &relations {
            if relation.target() as usize >= targets
                || relation.occurrence() as usize >= occurrences
                || relation.stood_before() == relation.stands_after()
            {
                return Err(ReturnedContactCudaError::InvalidFront);
            }
        }
        Ok(Self {
            targets,
            occurrences,
            relations,
        })
    }

    pub const fn targets(&self) -> usize {
        self.targets
    }

    pub const fn occurrences(&self) -> usize {
        self.occurrences
    }

    pub fn relations(&self) -> &[ReturnedContactRelation] {
        self.relations.as_ref()
    }
}

/// The complete exact cause grouping for one target.  Occurrence ordinals retain the caller's
/// atlas; no name or semantic identity is synthesized here.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ReturnedTargetGroup {
    pub target: u32,
    pub withdrawn_causes: LocalSequence<u32>,
    pub founded_causes: LocalSequence<u32>,
}

/// The card's independent disposition of one occurrence over the entire target population.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct ReturnedOccurrenceDisposition {
    pub occurrence: u32,
    pub withdrawn_targets: u32,
    pub founded_targets: u32,
}

impl ReturnedOccurrenceDisposition {
    pub const fn is_uncontacted(self) -> bool {
        self.withdrawn_targets == 0 && self.founded_targets == 0
    }
}

/// The semantic return.  This is separate from launch, allocation, and timing testimony.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ReturnedContactGroups {
    pub schema: String,
    pub targets: LocalSequence<ReturnedTargetGroup>,
    pub occurrences: LocalSequence<ReturnedOccurrenceDisposition>,
}

/// Physical testimony for one enactment.  None of these fields decides a contact.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ReturnedContactCudaReceipt {
    pub schema: String,
    pub device: String,
    pub layout_version: u32,
    pub launch_ordinal: u64,
    pub epoch: u32,
    pub epoch_reset: bool,
    pub targets: usize,
    pub occurrences: usize,
    pub relations: usize,
    pub occurrence_mask_words: usize,
    pub target_row_words: usize,
    pub header_relation_validations: usize,
    pub target_relation_tests: usize,
    pub occurrence_relation_tests: usize,
    pub host_to_device_words: usize,
    pub device_to_host_words: usize,
    pub returned_intermediate_relation_words: usize,
    pub kernel_launches: u32,
    pub device_zero_operations: u32,
    pub transient_allocation_operations: usize,
    pub grid: [u32; 3],
    pub block: [u32; 3],
    pub retained_streams: u32,
    pub stream_nonblocking: bool,
    pub stream_synchronizations: u32,
    pub prepare_and_ingress_nanoseconds: u128,
    pub kernel_and_stream_nanoseconds: u128,
    pub return_egress_nanoseconds: u128,
    pub elapsed_nanoseconds: u128,
}

pub struct ReturnedContactCudaOutput {
    pub semantic: ReturnedContactGroups,
    pub apparatus: ReturnedContactCudaReceipt,
}

/// One retained CUDA context/module with reusable relation and return apertures.  `context` is last
/// so every dependent allocation and module is released before its owning context.
pub struct CudaReturnedContactExecutor {
    module: Module,
    device_name: String,
    census: mount::cuda::LaunchCensus,
    launches: u64,
    epoch: u32,
    poisoned: bool,
    control: DeviceBuffer<u32>,
    relations: DeviceBuffer<u32>,
    output: DeviceBuffer<u32>,
    stream: Stream,
    context: Context,
}

impl CudaReturnedContactExecutor {
    pub fn new(device_ordinal: i32) -> Result<Self, ReturnedContactCudaError> {
        mount::cuda::init()?;
        let device = Device::get(device_ordinal)?;
        let census = device.launch_census()?;
        let context = Context::create(&device)?;
        let module = Module::load_ptx(SOMA_PTX)?;
        module.function(wire::ENTRY_SYMBOL)?;
        let control = DeviceBuffer::<u32>::alloc_zeroed(wire::CONTROL_WORDS)?;
        let relations = DeviceBuffer::<u32>::alloc_zeroed(1)?;
        let output = DeviceBuffer::<u32>::alloc_zeroed(wire::OUTPUT_HEADER_WORDS)?;
        let stream = Stream::create()?;
        Ok(Self {
            module,
            device_name: device.name,
            census,
            launches: 0,
            epoch: 0,
            poisoned: false,
            control,
            relations,
            output,
            stream,
            context,
        })
    }

    pub fn device_name(&self) -> &str {
        &self.device_name
    }

    pub const fn launches(&self) -> u64 {
        self.launches
    }

    pub const fn is_poisoned(&self) -> bool {
        self.poisoned
    }

    pub fn enact(
        &mut self,
        front: &ReturnedContactCudaFront,
    ) -> Result<ReturnedContactCudaOutput, ReturnedContactCudaError> {
        if self.poisoned {
            return Err(ReturnedContactCudaError::PoisonedRealization);
        }
        match self.enact_inner(front) {
            Ok(output) => Ok(output),
            Err(error) => {
                if error.poisons_realization() {
                    self.poisoned = true;
                }
                Err(error)
            }
        }
    }

    fn enact_inner(
        &mut self,
        front: &ReturnedContactCudaFront,
    ) -> Result<ReturnedContactCudaOutput, ReturnedContactCudaError> {
        self.context.make_current()?;
        let started = Instant::now();
        let (epoch, epoch_reset) = match self.epoch.checked_add(1) {
            Some(next) => (next, false),
            None => (1, true),
        };
        self.epoch = epoch;

        let control_words = wire::control(
            epoch,
            front.targets,
            front.occurrences,
            front.relations.len(),
        )
        .ok_or(ReturnedContactCudaError::Extent)?;
        let relation_extent = front
            .relations
            .len()
            .checked_mul(wire::RELATION_WORDS)
            .ok_or(ReturnedContactCudaError::Extent)?;
        let output_extent = wire::output_words(front.targets, front.occurrences)
            .ok_or(ReturnedContactCudaError::Extent)?;
        let mut relation_words = LocalSequence::with_capacity(relation_extent);
        for relation in &front.relations {
            let words = relation.words();
            for word in &words {
                relation_words.push(*word);
            }
        }

        let mut transient_allocation_operations = 0usize;
        if grow_buffer(&mut self.relations, relation_extent)? {
            transient_allocation_operations += 1;
        }
        if grow_buffer(&mut self.output, output_extent)? {
            transient_allocation_operations += 1;
        }
        self.control.copy_from_slice(&control_words)?;
        if !relation_words.is_empty() {
            self.relations
                .copy_range_from_slice(0, relation_words.as_ref())?;
        }
        self.output.zero()?;
        let prepare_and_ingress_nanoseconds = started.elapsed().as_nanos();

        let function = self.module.function(wire::ENTRY_SYMBOL)?;
        let work = 1u64
            .checked_add(
                u64::try_from(front.targets).map_err(|_| ReturnedContactCudaError::Extent)?,
            )
            .and_then(|extent| {
                u64::try_from(front.occurrences)
                    .ok()
                    .and_then(|occurrences| extent.checked_add(occurrences))
            })
            .ok_or(ReturnedContactCudaError::Extent)?;
        let launch = function.linear_launch(self.census, work)?;
        let mut control_pointer = self.control.device_ptr();
        let mut control_len = wire::CONTROL_WORDS;
        let mut relation_pointer = self.relations.device_ptr();
        let mut relation_len = relation_extent;
        let mut output_pointer = self.output.device_ptr();
        let mut output_len = output_extent;
        let mut x_stride = launch.x_stride;
        let mut parameters = [
            &mut control_pointer as *mut u64 as *mut c_void,
            &mut control_len as *mut usize as *mut c_void,
            &mut relation_pointer as *mut u64 as *mut c_void,
            &mut relation_len as *mut usize as *mut c_void,
            &mut output_pointer as *mut u64 as *mut c_void,
            &mut output_len as *mut usize as *mut c_void,
            &mut x_stride as *mut u32 as *mut c_void,
        ];
        let kernel_started = Instant::now();
        function.launch_on(&self.stream, launch.grid, launch.block, &mut parameters)?;
        self.stream.synchronize()?;
        let kernel_and_stream_nanoseconds = kernel_started.elapsed().as_nanos();

        let egress_started = Instant::now();
        let mut returned = LocalSequence::with_capacity(output_extent);
        returned.resize_with(output_extent, || 0);
        self.output.copy_range_to_slice(0, &mut returned)?;
        // Deliberately no relation argument: this decoder can only open the grouping the card
        // returned.  It cannot replay, transpose, or otherwise reconstruct the input relation.
        let semantic = decode_card_output(&control_words, returned.as_ref())?;
        let return_egress_nanoseconds = egress_started.elapsed().as_nanos();

        self.launches = self
            .launches
            .checked_add(1)
            .ok_or(ReturnedContactCudaError::Extent)?;
        let target_relation_tests = front
            .targets
            .checked_mul(front.relations.len())
            .ok_or(ReturnedContactCudaError::Extent)?;
        let occurrence_relation_tests = front
            .occurrences
            .checked_mul(front.relations.len())
            .ok_or(ReturnedContactCudaError::Extent)?;
        let apparatus = ReturnedContactCudaReceipt {
            schema: "soma-life.returned-contact-cuda-receipt.v1".to_owned(),
            device: self.device_name.to_owned(),
            layout_version: wire::LAYOUT_VERSION,
            launch_ordinal: self.launches,
            epoch,
            epoch_reset,
            targets: front.targets,
            occurrences: front.occurrences,
            relations: front.relations.len(),
            occurrence_mask_words: wire::mask_words(front.occurrences),
            target_row_words: wire::target_row_words(front.occurrences)
                .ok_or(ReturnedContactCudaError::Extent)?,
            header_relation_validations: front.relations.len(),
            target_relation_tests,
            occurrence_relation_tests,
            host_to_device_words: wire::CONTROL_WORDS
                .checked_add(relation_extent)
                .ok_or(ReturnedContactCudaError::Extent)?,
            device_to_host_words: output_extent,
            returned_intermediate_relation_words: 0,
            kernel_launches: 1,
            device_zero_operations: 1,
            transient_allocation_operations,
            grid: dimension_words(launch.grid),
            block: dimension_words(launch.block),
            retained_streams: 1,
            stream_nonblocking: self.stream.is_nonblocking(),
            stream_synchronizations: 1,
            prepare_and_ingress_nanoseconds,
            kernel_and_stream_nanoseconds,
            return_egress_nanoseconds,
            elapsed_nanoseconds: started.elapsed().as_nanos(),
        };
        Ok(ReturnedContactCudaOutput {
            semantic,
            apparatus,
        })
    }
}

impl Drop for CudaReturnedContactExecutor {
    fn drop(&mut self) {
        let _ = self.context.make_current();
    }
}

fn grow_buffer(
    buffer: &mut DeviceBuffer<u32>,
    required: usize,
) -> Result<bool, ReturnedContactCudaError> {
    let required = required.max(1);
    if buffer.len() >= required {
        return Ok(false);
    }
    let margin = (buffer.len() / 16).max(required - buffer.len()).max(64);
    let grown = buffer
        .len()
        .checked_add(margin)
        .map(|extent| extent.max(required))
        .ok_or(ReturnedContactCudaError::Extent)?;
    *buffer = DeviceBuffer::<u32>::alloc_zeroed(grown)?;
    Ok(true)
}

fn dimension_words(dimension: mount::Dim3) -> [u32; 3] {
    [dimension.x, dimension.y, dimension.z]
}

fn decode_card_output(
    control: &[u32],
    output: &[u32],
) -> Result<ReturnedContactGroups, ReturnedContactCudaError> {
    if !wire::control_is_canonical(control) || output.len() < wire::OUTPUT_HEADER_WORDS {
        return Err(ReturnedContactCudaError::InvalidDeviceReturn);
    }
    let targets = control[wire::CONTROL_TARGETS] as usize;
    let occurrences = control[wire::CONTROL_OCCURRENCES] as usize;
    let relations = control[wire::CONTROL_RELATIONS] as usize;
    let mask_words = wire::mask_words(occurrences);
    let target_row_words =
        wire::target_row_words(occurrences).ok_or(ReturnedContactCudaError::InvalidDeviceReturn)?;
    let occurrence_rows_at = wire::occurrence_rows_at(targets, occurrences)
        .ok_or(ReturnedContactCudaError::InvalidDeviceReturn)?;
    let expected_output = wire::output_words(targets, occurrences)
        .ok_or(ReturnedContactCudaError::InvalidDeviceReturn)?;
    if output.len() != expected_output {
        return Err(ReturnedContactCudaError::InvalidDeviceReturn);
    }
    match output[wire::OUTPUT_STATUS] {
        wire::STATUS_INVALID => {
            let relation = output[wire::OUTPUT_INVALID_RELATION];
            return Err(ReturnedContactCudaError::DeviceRefused {
                relation: (relation != wire::OPEN_RELATION).then_some(relation),
            });
        }
        wire::STATUS_COMPLETE => {}
        _ => return Err(ReturnedContactCudaError::InvalidDeviceReturn),
    }
    let header_matches = output[wire::OUTPUT_VERSION] == wire::LAYOUT_VERSION
        && output[wire::OUTPUT_EPOCH] == control[wire::CONTROL_EPOCH]
        && output[wire::OUTPUT_TARGETS] as usize == targets
        && output[wire::OUTPUT_OCCURRENCES] as usize == occurrences
        && output[wire::OUTPUT_RELATIONS] as usize == relations
        && output[wire::OUTPUT_OCCURRENCE_MASK_WORDS] as usize == mask_words
        && output[wire::OUTPUT_TARGET_ROW_WORDS] as usize == target_row_words
        && output[wire::OUTPUT_TARGET_ROWS_AT] as usize == wire::OUTPUT_HEADER_WORDS
        && output[wire::OUTPUT_OCCURRENCE_ROW_WORDS] as usize == wire::OCCURRENCE_ROW_WORDS
        && output[wire::OUTPUT_OCCURRENCE_ROWS_AT] as usize == occurrence_rows_at
        && output[wire::OUTPUT_TOTAL_WORDS] as usize == expected_output
        && output[wire::OUTPUT_INVALID_RELATION] == wire::OPEN_RELATION;
    if !header_matches {
        return Err(ReturnedContactCudaError::InvalidDeviceReturn);
    }

    let epoch = control[wire::CONTROL_EPOCH];
    let founded_mask_at = wire::target_founded_mask_at(occurrences)
        .ok_or(ReturnedContactCudaError::InvalidDeviceReturn)?;
    let mut target_groups = LocalSequence::with_capacity(targets);
    let mut target_relation_sum = 0usize;
    for target in 0..targets {
        let at = wire::OUTPUT_HEADER_WORDS + target * target_row_words;
        if output[at + wire::TARGET_STATUS] == wire::STATUS_INVALID {
            return Err(ReturnedContactCudaError::DeviceRefused { relation: None });
        }
        if output[at + wire::TARGET_STATUS] != wire::STATUS_COMPLETE
            || output[at + wire::TARGET_EPOCH] != epoch
            || output[at + wire::TARGET_ORDINAL] as usize != target
        {
            return Err(ReturnedContactCudaError::InvalidDeviceReturn);
        }
        let mut withdrawn_causes = LocalSequence::new();
        let mut founded_causes = LocalSequence::new();
        for occurrence in 0..occurrences {
            let word = occurrence / u32::BITS as usize;
            let bit = 1u32 << (occurrence % u32::BITS as usize);
            let withdrew = output[at + wire::TARGET_WITHDRAWN_MASK_AT + word] & bit != 0;
            let founded = output[at + founded_mask_at + word] & bit != 0;
            if withdrew && founded {
                return Err(ReturnedContactCudaError::InvalidDeviceReturn);
            }
            if withdrew {
                withdrawn_causes
                    .push(u32::try_from(occurrence).map_err(|_| ReturnedContactCudaError::Extent)?);
            }
            if founded {
                founded_causes
                    .push(u32::try_from(occurrence).map_err(|_| ReturnedContactCudaError::Extent)?);
            }
        }
        if mask_words > 0 && occurrences % u32::BITS as usize != 0 {
            let live_bits = occurrences % u32::BITS as usize;
            let unused = !((1u32 << live_bits) - 1);
            let last = mask_words - 1;
            if output[at + wire::TARGET_WITHDRAWN_MASK_AT + last] & unused != 0
                || output[at + founded_mask_at + last] & unused != 0
            {
                return Err(ReturnedContactCudaError::InvalidDeviceReturn);
            }
        }
        if output[at + wire::TARGET_WITHDRAWN] as usize != withdrawn_causes.len()
            || output[at + wire::TARGET_FOUNDED] as usize != founded_causes.len()
        {
            return Err(ReturnedContactCudaError::InvalidDeviceReturn);
        }
        target_relation_sum = target_relation_sum
            .checked_add(withdrawn_causes.len())
            .and_then(|sum| sum.checked_add(founded_causes.len()))
            .ok_or(ReturnedContactCudaError::Extent)?;
        target_groups.push(ReturnedTargetGroup {
            target: u32::try_from(target).map_err(|_| ReturnedContactCudaError::Extent)?,
            withdrawn_causes,
            founded_causes,
        });
    }

    let mut occurrence_dispositions = LocalSequence::with_capacity(occurrences);
    let mut occurrence_relation_sum = 0usize;
    for occurrence in 0..occurrences {
        let at = occurrence_rows_at + occurrence * wire::OCCURRENCE_ROW_WORDS;
        if output[at + wire::OCCURRENCE_STATUS] == wire::STATUS_INVALID {
            return Err(ReturnedContactCudaError::DeviceRefused { relation: None });
        }
        if output[at + wire::OCCURRENCE_STATUS] != wire::STATUS_COMPLETE
            || output[at + wire::OCCURRENCE_EPOCH] != epoch
            || output[at + wire::OCCURRENCE_ORDINAL] as usize != occurrence
        {
            return Err(ReturnedContactCudaError::InvalidDeviceReturn);
        }
        let withdrawn_targets = output[at + wire::OCCURRENCE_WITHDRAWN_TARGETS];
        let founded_targets = output[at + wire::OCCURRENCE_FOUNDED_TARGETS];
        if withdrawn_targets as usize > targets || founded_targets as usize > targets {
            return Err(ReturnedContactCudaError::InvalidDeviceReturn);
        }
        let occurrence_ordinal =
            u32::try_from(occurrence).map_err(|_| ReturnedContactCudaError::Extent)?;
        let mut withdrawn_from_target_masks = 0u32;
        let mut founded_from_target_masks = 0u32;
        for target in &target_groups {
            if target.withdrawn_causes.contains(&occurrence_ordinal) {
                withdrawn_from_target_masks = withdrawn_from_target_masks
                    .checked_add(1)
                    .ok_or(ReturnedContactCudaError::Extent)?;
            }
            if target.founded_causes.contains(&occurrence_ordinal) {
                founded_from_target_masks = founded_from_target_masks
                    .checked_add(1)
                    .ok_or(ReturnedContactCudaError::Extent)?;
            }
        }
        if withdrawn_targets != withdrawn_from_target_masks
            || founded_targets != founded_from_target_masks
        {
            return Err(ReturnedContactCudaError::InvalidDeviceReturn);
        }
        occurrence_relation_sum = occurrence_relation_sum
            .checked_add(withdrawn_targets as usize)
            .and_then(|sum| sum.checked_add(founded_targets as usize))
            .ok_or(ReturnedContactCudaError::Extent)?;
        occurrence_dispositions.push(ReturnedOccurrenceDisposition {
            occurrence: occurrence_ordinal,
            withdrawn_targets,
            founded_targets,
        });
    }
    if target_relation_sum != relations || occurrence_relation_sum != relations {
        return Err(ReturnedContactCudaError::InvalidDeviceReturn);
    }
    Ok(ReturnedContactGroups {
        schema: "soma-life.returned-contact-groups.v1".to_owned(),
        targets: target_groups,
        occurrences: occurrence_dispositions,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn relation(
        target: u32,
        occurrence: u32,
        stood_before: bool,
        stands_after: bool,
    ) -> ReturnedContactRelation {
        ReturnedContactRelation::new(target, occurrence, stood_before, stands_after)
            .expect("the test relation moves")
    }

    #[test]
    fn a_front_refuses_an_address_outside_its_declared_atlas() {
        let relations = LocalSequence::from([relation(2, 0, false, true)]);
        assert!(matches!(
            ReturnedContactCudaFront::new(2, 1, relations),
            Err(ReturnedContactCudaError::InvalidFront)
        ));
    }

    #[test]
    fn decoder_opens_only_card_groups_and_has_no_relation_population_to_replay() {
        let control = wire::control(7, 2, 3, 3).expect("control");
        let mut output =
            LocalSequence::with_capacity(wire::output_words(2, 3).expect("output extent"));
        output.resize_with(wire::output_words(2, 3).expect("output extent"), || 0);
        output[wire::OUTPUT_STATUS] = wire::STATUS_COMPLETE;
        output[wire::OUTPUT_VERSION] = wire::LAYOUT_VERSION;
        output[wire::OUTPUT_EPOCH] = 7;
        output[wire::OUTPUT_TARGETS] = 2;
        output[wire::OUTPUT_OCCURRENCES] = 3;
        output[wire::OUTPUT_RELATIONS] = 3;
        output[wire::OUTPUT_OCCURRENCE_MASK_WORDS] = 1;
        output[wire::OUTPUT_TARGET_ROW_WORDS] = 7;
        output[wire::OUTPUT_TARGET_ROWS_AT] = wire::OUTPUT_HEADER_WORDS as u32;
        output[wire::OUTPUT_OCCURRENCE_ROW_WORDS] = wire::OCCURRENCE_ROW_WORDS as u32;
        output[wire::OUTPUT_OCCURRENCE_ROWS_AT] = 27;
        output[wire::OUTPUT_TOTAL_WORDS] = output.len() as u32;
        output[wire::OUTPUT_INVALID_RELATION] = wire::OPEN_RELATION;

        let target_zero = wire::OUTPUT_HEADER_WORDS;
        output[target_zero + wire::TARGET_STATUS] = wire::STATUS_COMPLETE;
        output[target_zero + wire::TARGET_EPOCH] = 7;
        output[target_zero + wire::TARGET_ORDINAL] = 0;
        output[target_zero + wire::TARGET_WITHDRAWN] = 1;
        output[target_zero + wire::TARGET_FOUNDED] = 1;
        output[target_zero + wire::TARGET_WITHDRAWN_MASK_AT] = 1 << 2;
        output[target_zero + 6] = 1 << 0;

        let target_one = target_zero + 7;
        output[target_one + wire::TARGET_STATUS] = wire::STATUS_COMPLETE;
        output[target_one + wire::TARGET_EPOCH] = 7;
        output[target_one + wire::TARGET_ORDINAL] = 1;
        output[target_one + wire::TARGET_FOUNDED] = 1;
        output[target_one + 6] = 1 << 0;

        for occurrence in 0..3 {
            let at = 27 + occurrence * wire::OCCURRENCE_ROW_WORDS;
            output[at + wire::OCCURRENCE_STATUS] = wire::STATUS_COMPLETE;
            output[at + wire::OCCURRENCE_EPOCH] = 7;
            output[at + wire::OCCURRENCE_ORDINAL] = occurrence as u32;
        }
        output[27 + wire::OCCURRENCE_FOUNDED_TARGETS] = 2;
        output[27 + 2 * wire::OCCURRENCE_ROW_WORDS + wire::OCCURRENCE_WITHDRAWN_TARGETS] = 1;

        let groups = decode_card_output(&control, output.as_ref()).expect("card grouping opens");
        assert_eq!(groups.targets[0].withdrawn_causes.as_ref(), &[2]);
        assert_eq!(groups.targets[0].founded_causes.as_ref(), &[0]);
        assert_eq!(groups.targets[1].founded_causes.as_ref(), &[0]);
        assert!(groups.occurrences[1].is_uncontacted());

        let mut direction_forged = output;
        direction_forged[27 + wire::OCCURRENCE_WITHDRAWN_TARGETS] = 2;
        direction_forged[27 + wire::OCCURRENCE_FOUNDED_TARGETS] = 0;
        assert!(matches!(
            decode_card_output(&control, direction_forged.as_ref()),
            Err(ReturnedContactCudaError::InvalidDeviceReturn)
        ));
    }

    #[test]
    #[ignore = "requires a CUDA device and the committed returned_contact_group PTX entry"]
    fn card_groups_unsorted_movements_without_returning_the_relation_sheet() {
        let relations = LocalSequence::from([
            relation(2, 4, false, true),
            relation(0, 1, false, true),
            relation(2, 0, true, false),
            relation(0, 3, true, false),
            relation(1, 1, false, true),
        ]);
        let front = ReturnedContactCudaFront::new(3, 5, relations).expect("front");
        let mut cuda = CudaReturnedContactExecutor::new(0).expect("card mounts");
        let returned = cuda.enact(&front).expect("card groups");

        assert_eq!(returned.semantic.targets[0].withdrawn_causes.as_ref(), &[3]);
        assert_eq!(returned.semantic.targets[0].founded_causes.as_ref(), &[1]);
        assert_eq!(returned.semantic.targets[1].founded_causes.as_ref(), &[1]);
        assert_eq!(returned.semantic.targets[2].withdrawn_causes.as_ref(), &[0]);
        assert_eq!(returned.semantic.targets[2].founded_causes.as_ref(), &[4]);
        assert_eq!(returned.semantic.occurrences[0].withdrawn_targets, 1);
        assert_eq!(returned.semantic.occurrences[1].founded_targets, 2);
        assert!(returned.semantic.occurrences[2].is_uncontacted());
        assert_eq!(returned.apparatus.kernel_launches, 1);
        assert_eq!(returned.apparatus.returned_intermediate_relation_words, 0);
        assert_eq!(
            returned.apparatus.device_to_host_words,
            wire::output_words(3, 5).unwrap()
        );
    }

    #[test]
    #[ignore = "requires a CUDA device and the committed returned_contact_group PTX entry"]
    fn card_refuses_a_duplicate_local_relation() {
        let duplicate = relation(0, 0, false, true);
        let relations = LocalSequence::from([duplicate, duplicate]);
        let front = ReturnedContactCudaFront::new(1, 1, relations).expect("front");
        let mut cuda = CudaReturnedContactExecutor::new(0).expect("card mounts");
        assert!(matches!(
            cuda.enact(&front),
            Err(ReturnedContactCudaError::DeviceRefused { .. })
        ));
        assert!(!cuda.is_poisoned());
    }
}
