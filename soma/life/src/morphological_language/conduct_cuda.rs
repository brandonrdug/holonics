//! CUDA-owned candidate/deposit attachment for Plan-3 morphology conduct.
//!
//! This owner sits immediately before a caller forks sparse candidate currents.  The caller keeps
//! all ecological names and assigns dense candidate and deposit ordinals; the card receives two
//! independently assembled key sheets — every deposit's own exact transport key, and every key one
//! candidate could ride — and **decides membership itself** by searching the deposit sheet.  There
//! is deliberately no cpu fallback.
//!
//! **What changed at `LAYOUT_VERSION = 2`, and why.**  The first version shipped a cpu-built
//! `relation` sheet of `[candidate, deposit, face]` triples.  Building that sheet *is* the join:
//! the cpu had already asked, per candidate edge, which deposit ordinal it was, and the card
//! returned the identity on the answer while the cpu re-verified it.  One carrier, so no parity
//! was possible and the round trip was an echo.  The audit
//! (`research/records/2026-08-11_THE_SEAL_CARRIED_THE_CPU_AND_THE_ORGANS_AWAIT_THEIR_CURRENT.md`
//! §2 finding 4) named it, and it is withdrawn rather than deprecated.
//!
//! **The parity that is now possible.**  `cpu_attachment` recomputes the induced equivalence —
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
    /// cpu refuses it before the card does, and the card refuses it again.
    NoncanonicalSheet,
    DeviceRefused {
        key_row: Option<u32>,
    },
    /// The card declined the front before starting, and named which agreement failed. `declared`
    /// and `found` are the two extents where the check is an equality of extents.
    DeviceRefusedShape {
        cause: &'static str,
        declared: u32,
        found: u32,
    },
    /// No lane wrote a status word. This is NOT a disagreement about any field — it is the card
    /// having written nothing at all, and reporting it as a field disagreement is what sent one
    /// reader chasing a capacity that did not exist.
    DeviceWroteNothing,
    /// The card's return is malformed, and `at` names the exact check that disagreed. An
    /// opaque refusal at a membrane costs a rebuild-and-rerun cycle to locate; this names it.
    InvalidDeviceReturn {
        at: &'static str,
    },
    /// The card's induced equivalence and the cpu's independently recomputed one disagree.
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
            | (Self::PoisonedRealization, Self::PoisonedRealization) => true,
            (Self::InvalidDeviceReturn { at: left }, Self::InvalidDeviceReturn { at: right }) => {
                left == right
            }
            (Self::DeviceRefused { key_row: left }, Self::DeviceRefused { key_row: right }) => {
                left == right
            }
            (
                Self::DeviceRefusedShape { cause: left, .. },
                Self::DeviceRefusedShape { cause: right, .. },
            ) => left == right,
            (Self::DeviceWroteNothing, Self::DeviceWroteNothing) => true,
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
            Self::Driver(_)
                | Self::InvalidDeviceReturn { .. }
                | Self::DeviceWroteNothing
                | Self::ParityBroken { .. }
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
            Self::DeviceRefusedShape {
                cause,
                declared,
                found,
            } => write!(
                formatter,
                "the card declined the morphological-conduct front: {cause} (declared {declared}, \
                 found {found})"
            ),
            Self::DeviceWroteNothing => write!(
                formatter,
                "the card wrote no morphological-conduct status word"
            ),
            Self::InvalidDeviceReturn { at } => {
                write!(
                    formatter,
                    "the card returned malformed morphological-conduct attachment: {at}"
                )
            }
            Self::ParityBroken { candidate } => write!(
                formatter,
                "the card and the cpu disagree on the deposits candidate {candidate} attaches"
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
        self.deposits
            .iter()
            .filter(|deposit| deposit.active)
            .count()
    }

    /// **The independent cpu implementation of the same question, for parity only.**
    ///
    /// A linear merge rather than the card's binary search, returning the attached deposit **keys**
    /// per candidate. The comparison this feeds is of the induced equivalence — which keys each
    /// candidate rides — and never of the dense ordinals either side happens to use.
    pub fn cpu_attachment(&self) -> LocalSequence<LocalSequence<&[u32]>> {
        let mut cpu = LocalSequence::with_capacity(self.candidates.len());
        for _ in 0..self.candidates.len() {
            cpu.push(LocalSequence::new());
        }
        for row in &self.key_rows {
            for deposit in &self.deposits {
                if deposit.active && wire::key_equals(deposit.key(), row.key()) {
                    cpu[row.candidate as usize].push(deposit.key());
                    break;
                }
            }
        }
        cpu
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
    /// Compare the card's return with the cpu's independent recomputation, **of the induced
    /// equivalence**: the attached deposit keys per candidate, in canonical order.
    pub fn agrees_with(
        &self,
        front: &MorphologicalConductCudaFront,
    ) -> Result<(), MorphologicalConductCudaError> {
        let cpu = front.cpu_attachment();
        if cpu.len() != self.candidates.len() {
            return Err(MorphologicalConductCudaError::InvalidDeviceReturn {
                at: "the parity check received a different candidate population",
            });
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
                        .ok_or(MorphologicalConductCudaError::InvalidDeviceReturn {
                            at: "a returned deposit ordinal is outside the shipped sheet",
                        })
                })
                .collect::<Result<LocalSequence<_>, _>>()?;
            if device.len() != cpu[at].len()
                || device
                    .iter()
                    .zip(cpu[at].iter())
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
    /// What a linear cpu join would have cost on the same front, for the same reason.
    pub cpu_linear_comparison_cost: usize,
    pub cpu_to_device_words: usize,
    pub device_to_cpu_words: usize,
    pub kernel_launches: u32,
    pub device_zero_operations: u32,
    /// Default-stream barriers taken so a null-stream memset cannot race the launch stream.
    pub default_stream_barriers: u32,
    pub transient_allocation_operations: usize,
    pub grid: [u32; 3],
    pub block: [u32; 3],
    pub retained_streams: u32,
    pub stream_nonblocking: bool,
    pub stream_synchronizations: u32,
    pub cpu_parity_checked: bool,
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

/// Whether the cpu's independent recomputation runs beside every launch.
///
/// The parity test is the whole reason the device carrier is worth having, so it is on by default.
/// A caller producing at scale may declare it off; it is a caller's declaration with a stated
/// reason, never a silent optimisation, and the receipt carries which was in force.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MorphologicalConductParity {
    CpuRecomputesEveryLaunch,
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
            MorphologicalConductParity::CpuRecomputesEveryLaunch,
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

        // **The card is told what was UPLOADED, not what was declared.**
        //
        // These lengths used to be the declared extents, computed from the same control block the
        // card compares them against — so the card's sheet-extent agreements could not fail, and a
        // front whose keys were narrower than its declared width sailed through with the buffer's
        // zeroed tail read as key words. Passing the assembled length makes the agreement a real
        // check on a real quantity, and `card_names_the_agreement_it_declined_on` is the control
        // that proves the refusal reachable.
        let candidate_extent = candidate_words.len();
        let deposit_extent = deposit_words.len();
        let key_row_extent = key_row_words_sheet.len();

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
        // **The barrier between the null stream and the launch stream, and it is load-bearing.**
        //
        // `DeviceBuffer::zero` is `cuMemsetD32` on the context's DEFAULT stream, and this executor
        // launches on a stream created `CU_STREAM_NON_BLOCKING` — which by construction does not
        // synchronize with the default stream. The cpu-to-device copies above are `cuMemcpyHtoD`
        // on pageable memory and block the cpu until they land, so they need no barrier; the
        // memset does not, and without this the zeroing RACES the kernel.
        //
        // **Measured, and it is why this comment is here.** At two candidates and four deposits the
        // output is 12 to 48 words, the memset finishes instantly, and every small test passed. At
        // 4,096 candidates and 8,192 deposits the output is 73,740 words and the memset was still
        // running while lane 0 wrote the header: the card returned
        // `[1, 0, 0, 0, 0, 0, 5461, 0, 0, 0, 0, 0]` — status and active-deposit count intact
        // because lane 0 writes those AFTER its validation loops, and every straight-line header
        // word written before them zeroed back out. A silent wrong answer, invisible at the scale
        // the card tests used, which is `CLAUDE.md` §8's convicted shape exactly.
        //
        // `soma/life/src/returned_contact_cuda.rs:321` carries the same `zero()`-then-launch pattern
        // on a non-blocking stream and is outside this change's ownership; it is reported rather
        // than repaired here.
        self.context.synchronize()?;
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
        let semantic = decode_card_output(
            &control_words,
            returned.as_ref(),
            front.zero_active_ablation,
        )?;
        let return_egress_nanoseconds = egress_started.elapsed().as_nanos();

        let cpu_parity_checked =
            self.parity == MorphologicalConductParity::CpuRecomputesEveryLaunch;
        if cpu_parity_checked {
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
            cpu_linear_comparison_cost: front
                .key_rows
                .len()
                .checked_mul(front.deposits.len())
                .ok_or(MorphologicalConductCudaError::Extent)?,
            cpu_to_device_words: wire::CONTROL_WORDS
                .checked_add(candidate_extent)
                .and_then(|words| words.checked_add(deposit_extent))
                .and_then(|words| words.checked_add(key_row_extent))
                .ok_or(MorphologicalConductCudaError::Extent)?,
            device_to_cpu_words: output_extent,
            kernel_launches: 1,
            device_zero_operations: 1,
            default_stream_barriers: 1,
            transient_allocation_operations,
            grid: dimension_words(launch.grid),
            block: dimension_words(launch.block),
            retained_streams: 1,
            stream_nonblocking: self.stream.is_nonblocking(),
            stream_synchronizations: 1,
            cpu_parity_checked,
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
        return Err(MorphologicalConductCudaError::InvalidDeviceReturn {
            at: "control is not canonical, or the returned header is short",
        });
    }
    let candidates = control[wire::CONTROL_CANDIDATES] as usize;
    let deposits = control[wire::CONTROL_DEPOSITS] as usize;
    let key_rows = control[wire::CONTROL_KEY_ROWS] as usize;
    let max_candidate_keys = control[wire::CONTROL_MAX_CANDIDATE_KEYS] as usize;
    let row_words = wire::candidate_row_words(max_candidate_keys).ok_or(
        MorphologicalConductCudaError::InvalidDeviceReturn {
            at: "the candidate row width is not derivable from the control block",
        },
    )?;
    let expected_output = wire::output_words(candidates, max_candidate_keys).ok_or(
        MorphologicalConductCudaError::InvalidDeviceReturn {
            at: "the output extent is not derivable from the control block",
        },
    )?;
    if output.len() != expected_output {
        return Err(MorphologicalConductCudaError::InvalidDeviceReturn {
            at: "the returned extent is not the declared extent",
        });
    }
    match output[wire::OUTPUT_STATUS] {
        wire::STATUS_INVALID => {
            // A shape refusal names its own cause; a later refusal names the key row. They are
            // different returns and the cpu must not collapse them.
            let cause = output[wire::OUTPUT_REFUSAL_CAUSE];
            if cause != wire::REFUSAL_NONE {
                return Err(MorphologicalConductCudaError::DeviceRefusedShape {
                    cause: wire::refusal_cause_name(cause),
                    declared: output[wire::OUTPUT_REFUSAL_DECLARED],
                    found: output[wire::OUTPUT_REFUSAL_FOUND],
                });
            }
            let key_row = output[wire::OUTPUT_INVALID_KEY_ROW];
            return Err(MorphologicalConductCudaError::DeviceRefused {
                key_row: (key_row != wire::OPEN_KEY_ROW).then_some(key_row),
            });
        }
        wire::STATUS_COMPLETE => {}
        wire::STATUS_INCOMPLETE => return Err(MorphologicalConductCudaError::DeviceWroteNothing),
        _ => {
            return Err(MorphologicalConductCudaError::InvalidDeviceReturn {
                at: "the status word is not a declared status",
            })
        }
    }
    let active_deposits = output[wire::OUTPUT_ACTIVE_DEPOSITS];
    // **Named field by field, because one boolean over eleven checks costs a rebuild to locate.**
    // This is the same reason the refusal carries `at` at all: a membrane that says only "malformed"
    // makes every disagreement equally expensive, and at material scale that is where the defects
    // are.
    let header: [(&'static str, bool); 11] = [
        (
            "returned layout version",
            output[wire::OUTPUT_VERSION] == wire::LAYOUT_VERSION,
        ),
        (
            "returned epoch",
            output[wire::OUTPUT_EPOCH] == control[wire::CONTROL_EPOCH],
        ),
        (
            "returned candidate population",
            output[wire::OUTPUT_CANDIDATES] as usize == candidates,
        ),
        (
            "returned deposit population",
            output[wire::OUTPUT_DEPOSITS] as usize == deposits,
        ),
        (
            "returned key-row population",
            output[wire::OUTPUT_KEY_ROWS] as usize == key_rows,
        ),
        (
            "returned active-deposit count exceeds the deposit population",
            active_deposits as usize <= deposits,
        ),
        (
            "returned maximum candidate keys",
            output[wire::OUTPUT_MAX_CANDIDATE_KEYS] as usize == max_candidate_keys,
        ),
        (
            "returned candidate row width",
            output[wire::OUTPUT_CANDIDATE_ROW_WORDS] as usize == row_words,
        ),
        (
            "returned candidate rows offset",
            output[wire::OUTPUT_CANDIDATE_ROWS_AT] as usize == wire::OUTPUT_HEADER_WORDS,
        ),
        (
            "returned total words",
            output[wire::OUTPUT_TOTAL_WORDS] as usize == expected_output,
        ),
        (
            "returned invalid-key-row slot is not open",
            output[wire::OUTPUT_INVALID_KEY_ROW] == wire::OPEN_KEY_ROW,
        ),
    ];
    if let Some((at, _)) = header.iter().find(|(_, agrees)| !agrees) {
        return Err(MorphologicalConductCudaError::InvalidDeviceReturn { at });
    }
    if (active_deposits == 0) != zero_active_ablation {
        return Err(MorphologicalConductCudaError::InvalidDeviceReturn {
            at: "the zero-active-ablation declaration does not match what the card counted",
        });
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
            return Err(MorphologicalConductCudaError::InvalidDeviceReturn {
                at: "a candidate row is malformed: status, epoch, ordinal, face, match count, or \
                     key-row count",
            });
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
                    return Err(MorphologicalConductCudaError::InvalidDeviceReturn {
                        at: "a match slot is out of range or the matches are not strictly \
                             ascending",
                    });
                }
                active.push(word);
            } else if word != wire::OPEN_DEPOSIT {
                return Err(MorphologicalConductCudaError::InvalidDeviceReturn {
                    at: "an unused match slot carries a deposit",
                });
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
        return Err(MorphologicalConductCudaError::InvalidDeviceReturn {
            at: "the card's per-candidate key-row readings do not sum to the sheet it was given",
        });
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
    fn the_cpu_recomputation_attaches_by_key_and_skips_inactive_and_absent_keys() {
        let front = front();
        let cpu = front.cpu_attachment();
        // Candidate 0's second key names a deposit that exists but is inactive; candidate 1's third
        // key names no deposit at all. Neither attaches, and neither is an error.
        assert_eq!(cpu[0].len(), 1);
        assert_eq!(cpu[0][0], &[1, 0, 0]);
        assert_eq!(cpu[1].len(), 2);
        assert_eq!(cpu[1][0], &[2, 0, 0]);
        assert_eq!(cpu[1][1], &[2, 0, 1]);
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
        // And it agrees with the cpu's independent recomputation, of the keys and not the
        // ordinals.
        attachment.agrees_with(&front).expect("parity holds");

        let mut forged = output.clone();
        forged[first + wire::CANDIDATE_ACTIVE_DEPOSITS] = 2;
        assert!(matches!(
            decode_card_output(&control, forged.as_ref(), false),
            Err(MorphologicalConductCudaError::InvalidDeviceReturn { .. })
        ));

        // A card that read fewer key rows than were shipped is refused even when every match is
        // well formed.
        let mut short = output.clone();
        short[second + wire::CANDIDATE_KEY_ROWS] = 2;
        assert!(matches!(
            decode_card_output(&control, short.as_ref(), false),
            Err(MorphologicalConductCudaError::InvalidDeviceReturn { .. })
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
        assert!(returned.apparatus.cpu_parity_checked);
        // The carrier's own cost law: a binary search per key row against a linear join.
        assert!(
            returned.apparatus.deposit_search_comparison_bound
                < returned.apparatus.cpu_linear_comparison_cost
                || front.deposits().len() <= 4
        );
        returned
            .semantic
            .agrees_with(&front)
            .expect("card and cpu agree on the induced equivalence");

        let second = cuda.enact(&front).expect("card reuses executor");
        assert_eq!(second.apparatus.launch_ordinal, 2);
        assert_eq!(second.semantic, returned.semantic);
    }

    /// **A declared front larger than any the corpus has produced.**
    ///
    /// The three extents below are **authored by this test**, not read off anything: no material
    /// supplied 8,192 deposits or 4,096 candidates, and the largest real front measured so far
    /// carries 548 deposits. Calling them "material scale" would put the word that justifies a
    /// level on a level that has not earned it, so the name says what they are — a caller's
    /// declaration, chosen larger than the corpus reaches.
    ///
    /// It exists because the card tests above run two candidates against four deposits, and a card
    /// path proved at two candidates is proved at two candidates. It caught a real defect on its
    /// first run: `DeviceBuffer::zero` is a default-stream memset and the launch stream is
    /// non-blocking, so at 12 output words the zeroing landed first and at 73,740 it was still
    /// running while lane 0 wrote the header. See the barrier in `enact_inner`.
    #[test]
    fn card_carries_a_declared_front_larger_than_the_corpus_has_produced() {
        const KEY_WORDS: usize = 17;
        const DEPOSITS: usize = 8192;
        const CANDIDATES: usize = 4096;

        let key_of = |ordinal: u32| {
            let mut key = LocalSequence::with_capacity(KEY_WORDS);
            key.push(ordinal >> 16);
            key.push(ordinal & 0xffff);
            for word in 2..KEY_WORDS {
                key.push(word as u32);
            }
            key
        };
        let mut deposits = LocalSequence::with_capacity(DEPOSITS);
        for ordinal in 0..DEPOSITS {
            // Two thirds active, so the inactive ones are a real population rather than a corner.
            deposits.push(MorphologicalConductDepositRow::new(
                ordinal % 3 != 0,
                key_of(ordinal as u32 * 2),
            ));
        }
        let mut candidates = LocalSequence::with_capacity(CANDIDATES);
        let mut key_rows = LocalSequence::new();
        for candidate in 0..CANDIDATES {
            candidates
                .push(MorphologicalConductCandidate::new(1000 + candidate as u32).expect("face"));
            // Each candidate's keys are GENERATED ascending and distinct rather than sorted after
            // the fact: `LocalSet`/`LocalSequence` are the substrate's carriers and reaching for a
            // `Vec` to sort and dedup is what the ownership ratchet counts. Some keys land on a
            // deposit and some on nothing, because a candidate edge that is not deposited is the
            // ordinary case.
            let carried = candidate % 13;
            for step in 0..carried {
                // Strictly ascending in `step` and inside the key sheet's addressable range, so no
                // wrap can unsort a candidate's block. Deposits sit at even targets and 601 is odd,
                // so roughly half of these land on one and half on nothing.
                let target = candidate + step * 601;
                key_rows.push(MorphologicalConductCandidateKey::new(
                    candidate as u32,
                    key_of(target as u32),
                ));
            }
        }

        let front = MorphologicalConductCudaFront::new(KEY_WORDS, candidates, deposits, key_rows)
            .expect("a front at material scale is well formed");
        assert!(front.max_candidate_keys() >= 12);
        assert!(front.key_rows().len() > 20_000);

        let Ok(mut cuda) = CudaMorphologicalConductExecutor::new(0) else {
            eprintln!("no CUDA device: the material-scale card test did not run");
            return;
        };
        let returned = cuda
            .enact(&front)
            .expect("the card carries a front at material scale");
        assert_eq!(returned.semantic.candidates.len(), CANDIDATES);
        assert!(returned.apparatus.cpu_parity_checked);
        returned
            .semantic
            .agrees_with(&front)
            .expect("card and cpu agree on the induced equivalence at scale");
        // And the population it attached is neither empty nor everything, so the return separates.
        let attached: usize = returned
            .semantic
            .candidates
            .iter()
            .map(|candidate| candidate.active_deposits.len())
            .sum();
        assert!(attached > 0 && attached < front.key_rows().len());
    }

    /// **The named shape refusal, proved reachable rather than assumed.**
    ///
    /// A refusal nothing can reach is a check that cannot fail. This ships a front whose declared
    /// key width disagrees with the sheets it carries, which is a disagreement only the card can
    /// see, and requires the card to name it.
    #[test]
    fn card_names_the_agreement_it_declined_on() {
        let Ok(mut cuda) = CudaMorphologicalConductExecutor::new(0) else {
            eprintln!("no CUDA device: the named-refusal control did not run");
            return;
        };
        // Declared key width 4, sheets carrying 3-word keys. The cpu front type is bypassed
        // deliberately: its own `KeyWidth` guard would refuse this before the card saw it, and the
        // point is what the CARD says.
        let forged = MorphologicalConductCudaFront {
            key_words: 4,
            max_candidate_keys: 1,
            candidates: LocalSequence::from([candidate(FACE_A)]),
            deposits: LocalSequence::from([deposit(true, [1, 0, 0])]),
            key_rows: LocalSequence::from([key_row(0, [1, 0, 0])]),
            zero_active_ablation: false,
        };
        let refusal = cuda
            .enact(&forged)
            .expect_err("the card declines this front");
        let MorphologicalConductCudaError::DeviceRefusedShape {
            cause,
            declared,
            found,
        } = refusal
        else {
            panic!("the card must NAME the agreement it declined on, returned {refusal:?}");
        };
        assert_eq!(
            cause,
            "the deposit sheet the card received is not the declared extent"
        );
        assert_eq!(declared, 5);
        assert_eq!(found, 4);
        // A declined front does not poison the executor: the refusal is a return, not a fault.
        assert!(!cuda.is_poisoned());
    }

    #[test]
    fn card_refuses_a_forged_sheet_and_admits_explicit_zero_active_ablation() {
        let Ok(mut cuda) = CudaMorphologicalConductExecutor::new(0) else {
            eprintln!("no CUDA device: the morphological-conduct refusal test did not run");
            return;
        };
        // The cpu refuses a duplicated key row, so a forged front is built directly to prove the
        // card refuses it too rather than trusting the cpu's guard.
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
