//! CUDA-owned candidate/deposit attachment for Plan-3 morphology conduct.
//!
//! This owner sits immediately before a caller forks sparse candidate currents.  The caller keeps
//! all ecological names and assigns dense candidate and deposit ordinals; the card receives two
//! independently assembled key sheets — every deposit's own exact transport key, and every key one
//! candidate could ride — and **decides membership itself** by searching the deposit sheet.  There
//! is deliberately no host fallback.
//!
//! **What changed at `LAYOUT_VERSION = 2`, and why.**  The first version shipped a host-built
//! `relation` sheet of `[candidate, deposit, face]` triples.  Building that sheet *is* the join:
//! the host had already asked, per candidate edge, which deposit ordinal it was, and the card
//! returned the identity on the answer while the host re-verified it.  One carrier, so no parity
//! was possible and the round trip was an echo.  The audit
//! (`research/records/2026-08-11_THE_SEAL_CARRIED_THE_HOST_AND_THE_ORGANS_AWAIT_THEIR_CURRENT.md`
//! §2 finding 4) named it, and it is withdrawn rather than deprecated.
//!
//! **The parity that is now possible.**  `host_attachment` recomputes the induced equivalence —
//! which *keys* each candidate attaches, never which ordinals — from the same two sheets by an
//! independent implementation, and `MorphologicalConductAttachment::agrees_with` compares the two.
//! Equality is of the induced equivalence and not of the numbering.

use core::ffi::c_void;
use std::time::Instant;

use holonic_structure::{LocalSequence, LocalStructureError};
use mount::{Context, Device, DeviceBuffer, Module, Stream, SOMA_PTX};
use serde::Serialize;
use soma_abi::morphological_conduct_cuda as wire;
pub use soma_abi::morphological_conduct_cuda::MorphologicalConductCandidate;

#[derive(Clone, Debug)]
pub enum MorphologicalConductCudaError {
    Driver(mount::CudaError),
    Extent,
    InvalidFront,
    /// A key row or deposit row is not of the front's declared key width.
    KeyWidth,
    /// A sheet the card searches is not strictly ascending, so the search would be unsound. The
    /// host refuses it before the card does, and the card refuses it again.
    NoncanonicalSheet,
    DeviceRefused {
        key_row: Option<u32>,
    },
    InvalidDeviceReturn,
    /// The card's induced equivalence and the host's independently recomputed one disagree.
    ParityBroken {
        candidate: u32,
    },
    PoisonedRealization,
}

impl PartialEq for MorphologicalConductCudaError {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Driver(left), Self::Driver(right)) => {
                left.code == right.code
                    && left.name == right.name
                    && left.message == right.message
                    && left.context == right.context
            }
            (Self::Extent, Self::Extent)
            | (Self::InvalidFront, Self::InvalidFront)
            | (Self::KeyWidth, Self::KeyWidth)
            | (Self::NoncanonicalSheet, Self::NoncanonicalSheet)
            | (Self::InvalidDeviceReturn, Self::InvalidDeviceReturn)
            | (Self::PoisonedRealization, Self::PoisonedRealization) => true,
            (Self::DeviceRefused { key_row: left }, Self::DeviceRefused { key_row: right }) => {
                left == right
            }
            (
                Self::ParityBroken { candidate: left },
                Self::ParityBroken {
                    candidate: right, ..
                },
            ) => left == right,
            _ => false,
        }
    }
}

impl Eq for MorphologicalConductCudaError {}

impl MorphologicalConductCudaError {
    const fn poisons_realization(&self) -> bool {
        matches!(
            self,
            Self::Driver(_) | Self::InvalidDeviceReturn | Self::ParityBroken { .. }
        )
    }
}

impl std::fmt::Display for MorphologicalConductCudaError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Driver(error) => write!(formatter, "{error}"),
            Self::Extent => write!(
                formatter,
                "a morphological-conduct extent exceeded its exact wire"
            ),
            Self::InvalidFront => write!(formatter, "the morphological-conduct front is malformed"),
            Self::KeyWidth => write!(
                formatter,
                "a morphological-conduct key is not of the front's declared width"
            ),
            Self::NoncanonicalSheet => write!(
                formatter,
                "a morphological-conduct key sheet is not strictly ascending"
            ),
            Self::DeviceRefused {
                key_row: Some(key_row),
            } => write!(
                formatter,
                "the card refused morphological-conduct key row {key_row}"
            ),
            Self::DeviceRefused { key_row: None } => {
                write!(
                    formatter,
                    "the card refused the morphological-conduct front"
                )
            }
            Self::InvalidDeviceReturn => {
                write!(
                    formatter,
                    "the card returned malformed morphological-conduct attachment"
                )
            }
            Self::ParityBroken { candidate } => write!(
                formatter,
                "the card and the host disagree on the deposits candidate {candidate} attaches"
            ),
            Self::PoisonedRealization => {
                write!(
                    formatter,
                    "the morphological-conduct CUDA realization is poisoned"
                )
            }
        }
    }
}

impl std::error::Error for MorphologicalConductCudaError {}

impl From<mount::CudaError> for MorphologicalConductCudaError {
    fn from(error: mount::CudaError) -> Self {
        Self::Driver(error)
    }
}

impl From<LocalStructureError> for MorphologicalConductCudaError {
    fn from(_: LocalStructureError) -> Self {
        Self::Extent
    }
}

/// One deposit as the card sees it: an activity bit and the deposit's own exact transport key.
/// Nothing about which candidate might ride it is carried here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MorphologicalConductDepositRow {
    active: bool,
    key: LocalSequence<u32>,
}

impl MorphologicalConductDepositRow {
    pub const fn new(active: bool, key: LocalSequence<u32>) -> Self {
        Self { active, key }
    }

    pub const fn active(&self) -> bool {
        self.active
    }

    pub fn key(&self) -> &[u32] {
        self.key.as_ref()
    }
}

/// One key a candidate carries. Nothing about which deposit it might equal is carried here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MorphologicalConductCandidateKey {
    candidate: u32,
    key: LocalSequence<u32>,
}

impl MorphologicalConductCandidateKey {
    pub const fn new(candidate: u32, key: LocalSequence<u32>) -> Self {
        Self { candidate, key }
    }

    pub const fn candidate(&self) -> u32 {
        self.candidate
    }

    pub fn key(&self) -> &[u32] {
        self.key.as_ref()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MorphologicalConductCudaFront {
    key_words: usize,
    max_candidate_keys: usize,
    candidates: LocalSequence<MorphologicalConductCandidate>,
    deposits: LocalSequence<MorphologicalConductDepositRow>,
    key_rows: LocalSequence<MorphologicalConductCandidateKey>,
    zero_active_ablation: bool,
}

impl MorphologicalConductCudaFront {
    pub fn new(
        key_words: usize,
        candidates: LocalSequence<MorphologicalConductCandidate>,
        deposits: LocalSequence<MorphologicalConductDepositRow>,
        key_rows: LocalSequence<MorphologicalConductCandidateKey>,
    ) -> Result<Self, MorphologicalConductCudaError> {
        Self::build(key_words, candidates, deposits, key_rows, false)
    }

    pub fn explicit_zero_active_ablation(
        key_words: usize,
        candidates: LocalSequence<MorphologicalConductCandidate>,
        deposits: LocalSequence<MorphologicalConductDepositRow>,
        key_rows: LocalSequence<MorphologicalConductCandidateKey>,
    ) -> Result<Self, MorphologicalConductCudaError> {
        Self::build(key_words, candidates, deposits, key_rows, true)
    }

    fn build(
        key_words: usize,
        candidates: LocalSequence<MorphologicalConductCandidate>,
        deposits: LocalSequence<MorphologicalConductDepositRow>,
        key_rows: LocalSequence<MorphologicalConductCandidateKey>,
        zero_active_ablation: bool,
    ) -> Result<Self, MorphologicalConductCudaError> {
        if candidates.is_empty() || key_words == 0 {
            return Err(MorphologicalConductCudaError::InvalidFront);
        }
        u32::try_from(candidates.len()).map_err(|_| MorphologicalConductCudaError::Extent)?;
        u32::try_from(deposits.len()).map_err(|_| MorphologicalConductCudaError::Extent)?;
        u32::try_from(key_rows.len()).map_err(|_| MorphologicalConductCudaError::Extent)?;
        for deposit in &deposits {
            if deposit.key.len() != key_words {
                return Err(MorphologicalConductCudaError::KeyWidth);
            }
        }
        for pair in deposits.windows(2) {
            if !wire::key_precedes(pair[0].key(), pair[1].key()) {
                return Err(MorphologicalConductCudaError::NoncanonicalSheet);
            }
        }
        let mut max_candidate_keys = 0usize;
        let mut run = 0usize;
        for (at, row) in key_rows.iter().enumerate() {
            if row.key.len() != key_words {
                return Err(MorphologicalConductCudaError::KeyWidth);
            }
            if row.candidate as usize >= candidates.len() {
                return Err(MorphologicalConductCudaError::InvalidFront);
            }
            if at == 0 || key_rows[at - 1].candidate != row.candidate {
                if at > 0 && key_rows[at - 1].candidate > row.candidate {
                    return Err(MorphologicalConductCudaError::NoncanonicalSheet);
                }
                run = 0;
            } else if !wire::key_precedes(key_rows[at - 1].key(), row.key()) {
                return Err(MorphologicalConductCudaError::NoncanonicalSheet);
            }
            run += 1;
            max_candidate_keys = max_candidate_keys.max(run);
        }
        let active = deposits.iter().filter(|deposit| deposit.active).count();
        if (active == 0) != zero_active_ablation {
            return Err(MorphologicalConductCudaError::InvalidFront);
        }
        Ok(Self {
            key_words,
            max_candidate_keys,
            candidates,
            deposits,
            key_rows,
            zero_active_ablation,
        })
    }

    pub const fn key_words(&self) -> usize {
        self.key_words
    }

    pub const fn max_candidate_keys(&self) -> usize {
        self.max_candidate_keys
    }

    pub fn candidates(&self) -> &[MorphologicalConductCandidate] {
        self.candidates.as_ref()
    }

    pub fn deposits(&self) -> &[MorphologicalConductDepositRow] {
        self.deposits.as_ref()
    }

    pub fn key_rows(&self) -> &[MorphologicalConductCandidateKey] {
        self.key_rows.as_ref()
    }

    pub const fn zero_active_ablation(&self) -> bool {
        self.zero_active_ablation
    }

    pub fn active_deposits(&self) -> usize {
        self.deposits.iter().filter(|deposit| deposit.active).count()
    }

    /// **The independent host implementation of the same question, for parity only.**
    ///
    /// A linear merge rather than the card's binary search, returning the attached deposit **keys**
    /// per candidate. The comparison this feeds is of the induced equivalence — which keys each
    /// candidate rides — and never of the dense ordinals either side happens to use.
    pub fn host_attachment(&self) -> LocalSequence<LocalSequence<&[u32]>> {
        let mut host = LocalSequence::with_capacity(self.candidates.len());
        for _ in 0..self.candidates.len() {
            host.push(LocalSequence::new());
        }
        for row in &self.key_rows {
            for deposit in &self.deposits {
                if deposit.active && wire::key_equals(deposit.key(), row.key()) {
                    host[row.candidate as usize].push(deposit.key());
                    break;
                }
            }
        }
        host
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CandidateActiveDeposits {
    pub candidate: u32,
    pub face: u32,
    /// How many key rows the **card** read for this candidate.
    pub key_rows: u32,
    pub active_deposits: LocalSequence<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct MorphologicalConductAttachment {
    pub schema: String,
    pub candidates: LocalSequence<CandidateActiveDeposits>,
    pub active_deposits: u32,
    pub zero_active_ablation: bool,
}

impl MorphologicalConductAttachment {
    /// Compare the card's return with the host's independent recomputation, **of the induced
    /// equivalence**: the attached deposit keys per candidate, in canonical order.
    pub fn agrees_with(
        &self,
        front: &MorphologicalConductCudaFront,
    ) -> Result<(), MorphologicalConductCudaError> {
        let host = front.host_attachment();
        if host.len() != self.candidates.len() {
            return Err(MorphologicalConductCudaError::InvalidDeviceReturn);
        }
        for (at, returned) in self.candidates.iter().enumerate() {
            let device = returned
                .active_deposits
                .iter()
                .map(|deposit| {
                    front
                        .deposits
                        .get(*deposit as usize)
                        .map(MorphologicalConductDepositRow::key)
                        .ok_or(MorphologicalConductCudaError::InvalidDeviceReturn)
                })
                .collect::<Result<LocalSequence<_>, _>>()?;
            if device.len() != host[at].len()
                || device
                    .iter()
                    .zip(host[at].iter())
                    .any(|(left, right)| !wire::key_equals(left, right))
            {
                return Err(MorphologicalConductCudaError::ParityBroken {
                    candidate: returned.candidate,
                });
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct MorphologicalConductCudaReceipt {
    pub schema: String,
    pub device: String,
    pub layout_version: u32,
    pub launch_ordinal: u64,
    pub epoch: u32,
    pub epoch_reset: bool,
    pub candidates: usize,
    pub deposits: usize,
    pub active_deposits: usize,
    pub key_rows: usize,
    pub key_words: usize,
    pub max_candidate_keys: usize,
    pub zero_active_ablation: bool,
    pub candidate_row_words: usize,
    /// Sheet rows lane zero validated as strictly ascending before any lane searched.
    pub sheet_validations: usize,
    /// The exact bound on key comparisons the card's searches can perform: one binary search per
    /// key row over the deposit sheet. This is work, not time, and it reproduces on any machine.
    pub deposit_search_comparison_bound: usize,
    /// What a linear host join would have cost on the same front, for the same reason.
    pub host_linear_comparison_cost: usize,
    pub host_to_device_words: usize,
    pub device_to_host_words: usize,
    pub kernel_launches: u32,
    pub device_zero_operations: u32,
    pub transient_allocation_operations: usize,
    pub grid: [u32; 3],
    pub block: [u32; 3],
    pub retained_streams: u32,
    pub stream_nonblocking: bool,
    pub stream_synchronizations: u32,
    pub host_parity_checked: bool,
    pub prepare_and_ingress_nanoseconds: u128,
    pub kernel_and_stream_nanoseconds: u128,
    pub return_egress_nanoseconds: u128,
    pub elapsed_nanoseconds: u128,
}

#[derive(Debug)]
pub struct MorphologicalConductCudaOutput {
    pub semantic: MorphologicalConductAttachment,
    pub apparatus: MorphologicalConductCudaReceipt,
}

/// Whether the host's independent recomputation runs beside every launch.
///
/// The parity test is the whole reason the device carrier is worth having, so it is on by default.
/// A caller producing at scale may declare it off; it is a caller's declaration with a stated
/// reason, never a silent optimisation, and the receipt carries which was in force.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MorphologicalConductParity {
    HostRecomputesEveryLaunch,
    DeclaredOff,
}

pub struct CudaMorphologicalConductExecutor {
    module: Module,
    device_name: String,
    census: mount::cuda::LaunchCensus,
    launches: u64,
    epoch: u32,
    poisoned: bool,
    parity: MorphologicalConductParity,
    control: DeviceBuffer<u32>,
    candidates: DeviceBuffer<u32>,
    deposits: DeviceBuffer<u32>,
    key_rows: DeviceBuffer<u32>,
    output: DeviceBuffer<u32>,
    stream: Stream,
    context: Context,
}

impl CudaMorphologicalConductExecutor {
    pub fn new(device_ordinal: i32) -> Result<Self, MorphologicalConductCudaError> {
        Self::with_parity(
            device_ordinal,
            MorphologicalConductParity::HostRecomputesEveryLaunch,
        )
    }

    pub fn with_parity(
        device_ordinal: i32,
        parity: MorphologicalConductParity,
    ) -> Result<Self, MorphologicalConductCudaError> {
        mount::cuda::init()?;
        let device = Device::get(device_ordinal)?;
        let census = device.launch_census()?;
        let context = Context::create(&device)?;
        let module = Module::load_ptx(SOMA_PTX)?;
        module.function(wire::ENTRY_SYMBOL)?;
        let control = DeviceBuffer::<u32>::alloc_zeroed(wire::CONTROL_WORDS)?;
        let candidates = DeviceBuffer::<u32>::alloc_zeroed(1)?;
        let deposits = DeviceBuffer::<u32>::alloc_zeroed(1)?;
        let key_rows = DeviceBuffer::<u32>::alloc_zeroed(1)?;
        let output = DeviceBuffer::<u32>::alloc_zeroed(wire::OUTPUT_HEADER_WORDS)?;
        let stream = Stream::create()?;
        Ok(Self {
            module,
            device_name: device.name,
            census,
            launches: 0,
            epoch: 0,
            poisoned: false,
            parity,
            control,
            candidates,
            deposits,
            key_rows,
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

    pub const fn parity(&self) -> MorphologicalConductParity {
        self.parity
    }

    pub fn enact(
        &mut self,
        front: &MorphologicalConductCudaFront,
    ) -> Result<MorphologicalConductCudaOutput, MorphologicalConductCudaError> {
        if self.poisoned {
            return Err(MorphologicalConductCudaError::PoisonedRealization);
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
        front: &MorphologicalConductCudaFront,
    ) -> Result<MorphologicalConductCudaOutput, MorphologicalConductCudaError> {
        self.context.make_current()?;
        let started = Instant::now();
        let (epoch, epoch_reset) = match self.epoch.checked_add(1) {
            Some(next) => (next, false),
            None => (1, true),
        };
        self.epoch = epoch;

        let control_words = wire::control(
            epoch,
            front.candidates.len(),
            front.deposits.len(),
            front.key_rows.len(),
            front.key_words,
            front.max_candidate_keys,
        )
        .ok_or(MorphologicalConductCudaError::Extent)?;
        let deposit_row_words = wire::deposit_row_words(front.key_words)
            .ok_or(MorphologicalConductCudaError::Extent)?;
        let key_row_words =
            wire::key_row_words(front.key_words).ok_or(MorphologicalConductCudaError::Extent)?;
        let candidate_extent = front
            .candidates
            .len()
            .checked_mul(wire::CANDIDATE_WORDS)
            .ok_or(MorphologicalConductCudaError::Extent)?;
        let deposit_extent = front
            .deposits
            .len()
            .checked_mul(deposit_row_words)
            .ok_or(MorphologicalConductCudaError::Extent)?;
        let key_row_extent = front
            .key_rows
            .len()
            .checked_mul(key_row_words)
            .ok_or(MorphologicalConductCudaError::Extent)?;
        let output_extent = wire::output_words(front.candidates.len(), front.max_candidate_keys)
            .ok_or(MorphologicalConductCudaError::Extent)?;
        let mut candidate_words = LocalSequence::with_capacity(candidate_extent);
        for candidate in &front.candidates {
            for word in candidate.words() {
                candidate_words.push(word);
            }
        }
        let mut deposit_words = LocalSequence::with_capacity(deposit_extent);
        for deposit in &front.deposits {
            deposit_words.push(u32::from(deposit.active));
            for word in deposit.key() {
                deposit_words.push(*word);
            }
        }
        let mut key_row_words_sheet = LocalSequence::with_capacity(key_row_extent);
        for row in &front.key_rows {
            key_row_words_sheet.push(row.candidate);
            for word in row.key() {
                key_row_words_sheet.push(*word);
            }
        }

        let mut transient_allocation_operations = 0usize;
        if grow_buffer(&mut self.candidates, candidate_extent)? {
            transient_allocation_operations += 1;
        }
        if grow_buffer(&mut self.deposits, deposit_extent)? {
            transient_allocation_operations += 1;
        }
        if grow_buffer(&mut self.key_rows, key_row_extent)? {
            transient_allocation_operations += 1;
        }
        if grow_buffer(&mut self.output, output_extent)? {
            transient_allocation_operations += 1;
        }
        self.control.copy_from_slice(&control_words)?;
        if !candidate_words.is_empty() {
            self.candidates
                .copy_range_from_slice(0, candidate_words.as_ref())?;
        }
        if !deposit_words.is_empty() {
            self.deposits
                .copy_range_from_slice(0, deposit_words.as_ref())?;
        }
        if !key_row_words_sheet.is_empty() {
            self.key_rows
                .copy_range_from_slice(0, key_row_words_sheet.as_ref())?;
        }
        self.output.zero()?;
        let prepare_and_ingress_nanoseconds = started.elapsed().as_nanos();

        let function = self.module.function(wire::ENTRY_SYMBOL)?;
        let work = 1u64
            .checked_add(
                u64::try_from(front.candidates.len())
                    .map_err(|_| MorphologicalConductCudaError::Extent)?,
            )
            .ok_or(MorphologicalConductCudaError::Extent)?;
        let launch = function.linear_launch(self.census, work)?;
        let mut control_pointer = self.control.device_ptr();
        let mut control_len = wire::CONTROL_WORDS;
        let mut candidate_pointer = self.candidates.device_ptr();
        let mut candidate_len = candidate_extent;
        let mut deposit_pointer = self.deposits.device_ptr();
        let mut deposit_len = deposit_extent;
        let mut key_row_pointer = self.key_rows.device_ptr();
        let mut key_row_len = key_row_extent;
        let mut output_pointer = self.output.device_ptr();
        let mut output_len = output_extent;
        let mut x_stride = launch.x_stride;
        let mut parameters = [
            &mut control_pointer as *mut u64 as *mut c_void,
            &mut control_len as *mut usize as *mut c_void,
            &mut candidate_pointer as *mut u64 as *mut c_void,
            &mut candidate_len as *mut usize as *mut c_void,
            &mut deposit_pointer as *mut u64 as *mut c_void,
            &mut deposit_len as *mut usize as *mut c_void,
            &mut key_row_pointer as *mut u64 as *mut c_void,
            &mut key_row_len as *mut usize as *mut c_void,
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
        let semantic =
            decode_card_output(&control_words, returned.as_ref(), front.zero_active_ablation)?;
        let return_egress_nanoseconds = egress_started.elapsed().as_nanos();

        let host_parity_checked =
            self.parity == MorphologicalConductParity::HostRecomputesEveryLaunch;
        if host_parity_checked {
            semantic.agrees_with(front)?;
        }

        self.launches = self
            .launches
            .checked_add(1)
            .ok_or(MorphologicalConductCudaError::Extent)?;
        let search_bound = front
            .deposits
            .len()
            .checked_add(1)
            .map(usize::ilog2)
            .and_then(|bits| front.key_rows.len().checked_mul(bits as usize + 1))
            .ok_or(MorphologicalConductCudaError::Extent)?;
        let apparatus = MorphologicalConductCudaReceipt {
            schema: "soma-life.morphological-conduct-cuda-receipt.v2".to_owned(),
            device: self.device_name.to_owned(),
            layout_version: wire::LAYOUT_VERSION,
            launch_ordinal: self.launches,
            epoch,
            epoch_reset,
            candidates: front.candidates.len(),
            deposits: front.deposits.len(),
            active_deposits: front.active_deposits(),
            key_rows: front.key_rows.len(),
            key_words: front.key_words,
            max_candidate_keys: front.max_candidate_keys,
            zero_active_ablation: front.zero_active_ablation,
            candidate_row_words: wire::candidate_row_words(front.max_candidate_keys)
                .ok_or(MorphologicalConductCudaError::Extent)?,
            sheet_validations: front
                .deposits
                .len()
                .checked_add(front.key_rows.len())
                .ok_or(MorphologicalConductCudaError::Extent)?,
            deposit_search_comparison_bound: search_bound,
            host_linear_comparison_cost: front
                .key_rows
                .len()
                .checked_mul(front.deposits.len())
                .ok_or(MorphologicalConductCudaError::Extent)?,
            host_to_device_words: wire::CONTROL_WORDS
                .checked_add(candidate_extent)
                .and_then(|words| words.checked_add(deposit_extent))
                .and_then(|words| words.checked_add(key_row_extent))
                .ok_or(MorphologicalConductCudaError::Extent)?,
            device_to_host_words: output_extent,
            kernel_launches: 1,
            device_zero_operations: 1,
            transient_allocation_operations,
            grid: dimension_words(launch.grid),
            block: dimension_words(launch.block),
            retained_streams: 1,
            stream_nonblocking: self.stream.is_nonblocking(),
            stream_synchronizations: 1,
            host_parity_checked,
            prepare_and_ingress_nanoseconds,
            kernel_and_stream_nanoseconds,
            return_egress_nanoseconds,
            elapsed_nanoseconds: started.elapsed().as_nanos(),
        };
        Ok(MorphologicalConductCudaOutput {
            semantic,
            apparatus,
        })
    }
}

impl Drop for CudaMorphologicalConductExecutor {
    fn drop(&mut self) {
        let _ = self.context.make_current();
    }
}

/// **Grow to exactly what the material asks for.**
///
/// This carried `(buffer.len() / 16).max(required - buffer.len()).max(64)` — a growth ratio and a
/// floor, two authored levels no caller declared and no material supplied, copied from a sibling
/// executor. The extent a launch needs *is* the material's extent, so the buffer grows to it and to
/// nothing else; the reallocation count is already a measured receipt
/// (`transient_allocation_operations`) rather than a number to be hidden by a margin. A buffer
/// never shrinks, so a front smaller than an earlier one still reallocates nothing.
fn grow_buffer(
    buffer: &mut DeviceBuffer<u32>,
    required: usize,
) -> Result<bool, MorphologicalConductCudaError> {
    let required = required.max(1);
    if buffer.len() >= required {
        return Ok(false);
    }
    *buffer = DeviceBuffer::<u32>::alloc_zeroed(required)?;
    Ok(true)
}

fn dimension_words(dimension: mount::Dim3) -> [u32; 3] {
    [dimension.x, dimension.y, dimension.z]
}

fn decode_card_output(
    control: &[u32],
    output: &[u32],
    zero_active_ablation: bool,
) -> Result<MorphologicalConductAttachment, MorphologicalConductCudaError> {
    if !wire::control_is_canonical(control) || output.len() < wire::OUTPUT_HEADER_WORDS {
        return Err(MorphologicalConductCudaError::InvalidDeviceReturn);
    }
    let candidates = control[wire::CONTROL_CANDIDATES] as usize;
    let deposits = control[wire::CONTROL_DEPOSITS] as usize;
    let key_rows = control[wire::CONTROL_KEY_ROWS] as usize;
    let max_candidate_keys = control[wire::CONTROL_MAX_CANDIDATE_KEYS] as usize;
    let row_words = wire::candidate_row_words(max_candidate_keys)
        .ok_or(MorphologicalConductCudaError::InvalidDeviceReturn)?;
    let expected_output = wire::output_words(candidates, max_candidate_keys)
        .ok_or(MorphologicalConductCudaError::InvalidDeviceReturn)?;
    if output.len() != expected_output {
        return Err(MorphologicalConductCudaError::InvalidDeviceReturn);
    }
    match output[wire::OUTPUT_STATUS] {
        wire::STATUS_INVALID => {
            let key_row = output[wire::OUTPUT_INVALID_KEY_ROW];
            return Err(MorphologicalConductCudaError::DeviceRefused {
                key_row: (key_row != wire::OPEN_KEY_ROW).then_some(key_row),
            });
        }
        wire::STATUS_COMPLETE => {}
        _ => return Err(MorphologicalConductCudaError::InvalidDeviceReturn),
    }
    let active_deposits = output[wire::OUTPUT_ACTIVE_DEPOSITS];
    let header_matches = output[wire::OUTPUT_VERSION] == wire::LAYOUT_VERSION
        && output[wire::OUTPUT_EPOCH] == control[wire::CONTROL_EPOCH]
        && output[wire::OUTPUT_CANDIDATES] as usize == candidates
        && output[wire::OUTPUT_DEPOSITS] as usize == deposits
        && output[wire::OUTPUT_KEY_ROWS] as usize == key_rows
        && active_deposits as usize <= deposits
        && output[wire::OUTPUT_MAX_CANDIDATE_KEYS] as usize == max_candidate_keys
        && output[wire::OUTPUT_CANDIDATE_ROW_WORDS] as usize == row_words
        && output[wire::OUTPUT_CANDIDATE_ROWS_AT] as usize == wire::OUTPUT_HEADER_WORDS
        && output[wire::OUTPUT_TOTAL_WORDS] as usize == expected_output
        && output[wire::OUTPUT_INVALID_KEY_ROW] == wire::OPEN_KEY_ROW;
    if !header_matches || (active_deposits == 0) != zero_active_ablation {
        return Err(MorphologicalConductCudaError::InvalidDeviceReturn);
    }
    let mut returned_candidates = LocalSequence::with_capacity(candidates);
    let mut total_key_rows = 0usize;
    for candidate in 0..candidates {
        let at = wire::OUTPUT_HEADER_WORDS + candidate * row_words;
        if output[at + wire::CANDIDATE_STATUS] == wire::STATUS_INVALID {
            return Err(MorphologicalConductCudaError::DeviceRefused { key_row: None });
        }
        let carried = output[at + wire::CANDIDATE_ACTIVE_DEPOSITS] as usize;
        if output[at + wire::CANDIDATE_STATUS] != wire::STATUS_COMPLETE
            || output[at + wire::CANDIDATE_EPOCH] != control[wire::CONTROL_EPOCH]
            || output[at + wire::CANDIDATE_ORDINAL] as usize != candidate
            || output[at + wire::CANDIDATE_OUTPUT_FACE] == wire::OPEN_FACE
            || carried > max_candidate_keys
            || output[at + wire::CANDIDATE_KEY_ROWS] as usize > key_rows
        {
            return Err(MorphologicalConductCudaError::InvalidDeviceReturn);
        }
        total_key_rows = total_key_rows
            .checked_add(output[at + wire::CANDIDATE_KEY_ROWS] as usize)
            .ok_or(MorphologicalConductCudaError::Extent)?;
        let mut active = LocalSequence::with_capacity(carried);
        for slot in 0..max_candidate_keys {
            let word = output[at + wire::CANDIDATE_MATCH_AT + slot];
            if slot < carried {
                if word as usize >= deposits
                    || active
                        .last()
                        .is_some_and(|previous: &u32| *previous >= word)
                {
                    return Err(MorphologicalConductCudaError::InvalidDeviceReturn);
                }
                active.push(word);
            } else if word != wire::OPEN_DEPOSIT {
                return Err(MorphologicalConductCudaError::InvalidDeviceReturn);
            }
        }
        returned_candidates.push(CandidateActiveDeposits {
            candidate: u32::try_from(candidate)
                .map_err(|_| MorphologicalConductCudaError::Extent)?,
            face: output[at + wire::CANDIDATE_OUTPUT_FACE],
            key_rows: output[at + wire::CANDIDATE_KEY_ROWS],
            active_deposits: active,
        });
    }
    // Every key row belongs to exactly one candidate, so the card's own per-candidate readings must
    // sum to the sheet it was given. This is the card saying what it read, checked against what was
    // shipped.
    if total_key_rows != key_rows {
        return Err(MorphologicalConductCudaError::InvalidDeviceReturn);
    }
    Ok(MorphologicalConductAttachment {
        schema: "soma-life.morphological-conduct-attachment.v2".to_owned(),
        candidates: returned_candidates,
        active_deposits,
        zero_active_ablation,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const FACE_A: u32 = 0x415;
    const FACE_B: u32 = 0x816;

    fn candidate(face: u32) -> MorphologicalConductCandidate {
        MorphologicalConductCandidate::new(face).expect("candidate face")
    }

    fn key(words: [u32; 3]) -> LocalSequence<u32> {
        LocalSequence::from(words)
    }

    fn deposit(active: bool, words: [u32; 3]) -> MorphologicalConductDepositRow {
        MorphologicalConductDepositRow::new(active, key(words))
    }

    fn key_row(candidate: u32, words: [u32; 3]) -> MorphologicalConductCandidateKey {
        MorphologicalConductCandidateKey::new(candidate, key(words))
    }

    fn front() -> MorphologicalConductCudaFront {
        MorphologicalConductCudaFront::new(
            3,
            LocalSequence::from([candidate(FACE_A), candidate(FACE_B)]),
            LocalSequence::from([
                deposit(true, [1, 0, 0]),
                deposit(false, [1, 0, 1]),
                deposit(true, [2, 0, 0]),
                deposit(true, [2, 0, 1]),
            ]),
            LocalSequence::from([
                key_row(0, [1, 0, 0]),
                key_row(0, [1, 0, 1]),
                key_row(1, [2, 0, 0]),
                key_row(1, [2, 0, 1]),
                key_row(1, [9, 9, 9]),
            ]),
        )
        .expect("front")
    }

    #[test]
    fn front_refuses_wrong_key_width_out_of_range_owner_and_unsorted_sheets() {
        assert_eq!(
            MorphologicalConductCudaFront::new(
                3,
                LocalSequence::from([candidate(FACE_A)]),
                LocalSequence::from([deposit(true, [1, 0, 0])]),
                LocalSequence::from([MorphologicalConductCandidateKey::new(
                    0,
                    LocalSequence::from([1, 0])
                )]),
            ),
            Err(MorphologicalConductCudaError::KeyWidth)
        );
        assert_eq!(
            MorphologicalConductCudaFront::new(
                3,
                LocalSequence::from([candidate(FACE_A)]),
                LocalSequence::from([deposit(true, [1, 0, 0])]),
                LocalSequence::from([key_row(1, [1, 0, 0])]),
            ),
            Err(MorphologicalConductCudaError::InvalidFront)
        );
        assert_eq!(
            MorphologicalConductCudaFront::new(
                3,
                LocalSequence::from([candidate(FACE_A)]),
                LocalSequence::from([deposit(true, [2, 0, 0]), deposit(true, [1, 0, 0])]),
                LocalSequence::from([key_row(0, [1, 0, 0])]),
            ),
            Err(MorphologicalConductCudaError::NoncanonicalSheet)
        );
        assert_eq!(
            MorphologicalConductCudaFront::new(
                3,
                LocalSequence::from([candidate(FACE_A)]),
                LocalSequence::from([deposit(true, [1, 0, 0])]),
                LocalSequence::from([key_row(0, [1, 0, 1]), key_row(0, [1, 0, 0])]),
            ),
            Err(MorphologicalConductCudaError::NoncanonicalSheet)
        );
        assert_eq!(
            MorphologicalConductCudaFront::new(
                3,
                LocalSequence::from([candidate(FACE_A)]),
                LocalSequence::from([deposit(false, [1, 0, 0])]),
                LocalSequence::from([key_row(0, [1, 0, 0])]),
            ),
            Err(MorphologicalConductCudaError::InvalidFront)
        );
    }

    #[test]
    fn the_front_reads_its_own_widths_off_the_material() {
        let front = front();
        assert_eq!(front.key_words(), 3);
        // Candidate 1 carries three keys, candidate 0 carries two: the returned row width is the
        // larger, read off the front rather than declared.
        assert_eq!(front.max_candidate_keys(), 3);
        assert_eq!(front.active_deposits(), 3);
    }

    #[test]
    fn the_host_recomputation_attaches_by_key_and_skips_inactive_and_absent_keys() {
        let front = front();
        let host = front.host_attachment();
        // Candidate 0's second key names a deposit that exists but is inactive; candidate 1's third
        // key names no deposit at all. Neither attaches, and neither is an error.
        assert_eq!(host[0].len(), 1);
        assert_eq!(host[0][0], &[1, 0, 0]);
        assert_eq!(host[1].len(), 2);
        assert_eq!(host[1][0], &[2, 0, 0]);
        assert_eq!(host[1][1], &[2, 0, 1]);
    }

    #[test]
    fn decoder_opens_only_card_match_slots_and_refuses_a_forged_count() {
        let front = front();
        let control = wire::control(9, 2, 4, 5, 3, 3).expect("control");
        let extent = wire::output_words(2, 3).expect("output extent");
        let mut output = LocalSequence::with_capacity(extent);
        output.resize_with(extent, || 0);
        output[wire::OUTPUT_STATUS] = wire::STATUS_COMPLETE;
        output[wire::OUTPUT_VERSION] = wire::LAYOUT_VERSION;
        output[wire::OUTPUT_EPOCH] = 9;
        output[wire::OUTPUT_CANDIDATES] = 2;
        output[wire::OUTPUT_DEPOSITS] = 4;
        output[wire::OUTPUT_KEY_ROWS] = 5;
        output[wire::OUTPUT_ACTIVE_DEPOSITS] = 3;
        output[wire::OUTPUT_MAX_CANDIDATE_KEYS] = 3;
        output[wire::OUTPUT_CANDIDATE_ROW_WORDS] = 9;
        output[wire::OUTPUT_CANDIDATE_ROWS_AT] = wire::OUTPUT_HEADER_WORDS as u32;
        output[wire::OUTPUT_TOTAL_WORDS] = extent as u32;
        output[wire::OUTPUT_INVALID_KEY_ROW] = wire::OPEN_KEY_ROW;

        let first = wire::OUTPUT_HEADER_WORDS;
        output[first + wire::CANDIDATE_STATUS] = wire::STATUS_COMPLETE;
        output[first + wire::CANDIDATE_EPOCH] = 9;
        output[first + wire::CANDIDATE_ORDINAL] = 0;
        output[first + wire::CANDIDATE_OUTPUT_FACE] = FACE_A;
        output[first + wire::CANDIDATE_KEY_ROWS] = 2;
        output[first + wire::CANDIDATE_ACTIVE_DEPOSITS] = 1;
        output[first + wire::CANDIDATE_MATCH_AT] = 0;
        output[first + wire::CANDIDATE_MATCH_AT + 1] = wire::OPEN_DEPOSIT;
        output[first + wire::CANDIDATE_MATCH_AT + 2] = wire::OPEN_DEPOSIT;

        let second = first + 9;
        output[second + wire::CANDIDATE_STATUS] = wire::STATUS_COMPLETE;
        output[second + wire::CANDIDATE_EPOCH] = 9;
        output[second + wire::CANDIDATE_ORDINAL] = 1;
        output[second + wire::CANDIDATE_OUTPUT_FACE] = FACE_B;
        output[second + wire::CANDIDATE_KEY_ROWS] = 3;
        output[second + wire::CANDIDATE_ACTIVE_DEPOSITS] = 2;
        output[second + wire::CANDIDATE_MATCH_AT] = 2;
        output[second + wire::CANDIDATE_MATCH_AT + 1] = 3;
        output[second + wire::CANDIDATE_MATCH_AT + 2] = wire::OPEN_DEPOSIT;

        let attachment =
            decode_card_output(&control, output.as_ref(), false).expect("card matches open");
        assert_eq!(attachment.active_deposits, 3);
        assert_eq!(attachment.candidates[0].active_deposits.as_ref(), &[0]);
        assert_eq!(attachment.candidates[1].active_deposits.as_ref(), &[2, 3]);
        // And it agrees with the host's independent recomputation, of the keys and not the
        // ordinals.
        attachment.agrees_with(&front).expect("parity holds");

        let mut forged = output.clone();
        forged[first + wire::CANDIDATE_ACTIVE_DEPOSITS] = 2;
        assert!(matches!(
            decode_card_output(&control, forged.as_ref(), false),
            Err(MorphologicalConductCudaError::InvalidDeviceReturn)
        ));

        // A card that read fewer key rows than were shipped is refused even when every match is
        // well formed.
        let mut short = output.clone();
        short[second + wire::CANDIDATE_KEY_ROWS] = 2;
        assert!(matches!(
            decode_card_output(&control, short.as_ref(), false),
            Err(MorphologicalConductCudaError::InvalidDeviceReturn)
        ));

        // And a well-formed return that attaches the wrong deposit fails parity rather than
        // decoding, which is the check the echo could not carry.
        let mut swapped = output;
        swapped[first + wire::CANDIDATE_MATCH_AT] = 2;
        let decoded =
            decode_card_output(&control, swapped.as_ref(), false).expect("shape is still valid");
        assert_eq!(
            decoded.agrees_with(&front),
            Err(MorphologicalConductCudaError::ParityBroken { candidate: 0 })
        );
    }

    #[test]
    fn card_decides_membership_from_two_independent_key_sheets() {
        let Ok(mut cuda) = CudaMorphologicalConductExecutor::new(0) else {
            eprintln!("no CUDA device: the morphological-conduct card test did not run");
            return;
        };
        let front = front();
        let returned = cuda.enact(&front).expect("card attaches");
        assert_eq!(returned.semantic.active_deposits, 3);
        assert_eq!(
            returned.semantic.candidates[0].active_deposits.as_ref(),
            &[0]
        );
        assert_eq!(
            returned.semantic.candidates[1].active_deposits.as_ref(),
            &[2, 3]
        );
        assert_eq!(returned.semantic.candidates[0].key_rows, 2);
        assert_eq!(returned.semantic.candidates[1].key_rows, 3);
        assert_eq!(returned.apparatus.kernel_launches, 1);
        assert_eq!(returned.apparatus.launch_ordinal, 1);
        assert!(returned.apparatus.host_parity_checked);
        // The carrier's own cost law: a binary search per key row against a linear join.
        assert!(
            returned.apparatus.deposit_search_comparison_bound
                < returned.apparatus.host_linear_comparison_cost
                || front.deposits().len() <= 4
        );
        returned
            .semantic
            .agrees_with(&front)
            .expect("card and host agree on the induced equivalence");

        let second = cuda.enact(&front).expect("card reuses executor");
        assert_eq!(second.apparatus.launch_ordinal, 2);
        assert_eq!(second.semantic, returned.semantic);
    }

    #[test]
    fn card_refuses_a_forged_sheet_and_admits_explicit_zero_active_ablation() {
        let Ok(mut cuda) = CudaMorphologicalConductExecutor::new(0) else {
            eprintln!("no CUDA device: the morphological-conduct refusal test did not run");
            return;
        };
        // The host refuses a duplicated key row, so a forged front is built directly to prove the
        // card refuses it too rather than trusting the host's guard.
        let forged = MorphologicalConductCudaFront {
            key_words: 3,
            max_candidate_keys: 2,
            candidates: LocalSequence::from([candidate(FACE_A)]),
            deposits: LocalSequence::from([deposit(true, [1, 0, 0])]),
            key_rows: LocalSequence::from([key_row(0, [1, 0, 0]), key_row(0, [1, 0, 0])]),
            zero_active_ablation: false,
        };
        assert_eq!(
            cuda.enact(&forged).err(),
            Some(MorphologicalConductCudaError::DeviceRefused { key_row: Some(1) })
        );
        assert!(!cuda.is_poisoned());

        let out_of_range = MorphologicalConductCudaFront {
            key_words: 3,
            max_candidate_keys: 1,
            candidates: LocalSequence::from([candidate(FACE_A)]),
            deposits: LocalSequence::from([deposit(true, [1, 0, 0])]),
            key_rows: LocalSequence::from([key_row(4, [1, 0, 0])]),
            zero_active_ablation: false,
        };
        assert_eq!(
            cuda.enact(&out_of_range).err(),
            Some(MorphologicalConductCudaError::DeviceRefused { key_row: Some(0) })
        );

        let ablation = MorphologicalConductCudaFront::explicit_zero_active_ablation(
            3,
            LocalSequence::from([candidate(FACE_A)]),
            LocalSequence::from([deposit(false, [1, 0, 0])]),
            LocalSequence::from([key_row(0, [1, 0, 0])]),
        )
        .expect("explicit ablation");
        let returned = cuda.enact(&ablation).expect("zero-active card testimony");
        assert_eq!(returned.semantic.active_deposits, 0);
        assert!(returned.semantic.zero_active_ablation);
        assert!(returned.semantic.candidates[0].active_deposits.is_empty());
        // The card still read the key row; it found the deposit and refused it for being inactive.
        assert_eq!(returned.semantic.candidates[0].key_rows, 1);
    }
}
