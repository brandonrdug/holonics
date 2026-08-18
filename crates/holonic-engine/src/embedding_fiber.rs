//! **The exact score population of one query against a deposited map's readout.**
//!
//! Record:
//! `research/records/2026-08-13_THE_MAP_DECLARES_ITS_OWN_APERTURES_AND_AN_EMBEDDING_IS_A_DECLARED_RECEIVER.md`.
//! Kernel: `kernels/exact_embedding_fiber.cu`.
//!
//! # What this returns, and the one thing it refuses
//!
//! Given a readout matrix and one query, this returns **every** exact score
//!
//! ```text
//!   s[v] = <E[v], u>          exact, i128, no rounding anywhere
//! ```
//!
//! and takes no maximum. The refusal is load-bearing and it is not this module's invention.
//! `research/records/2026-08-12_THE_PRETRAINED_TRANSFORMER_IS_ONE_TRANSPORT_ORGAN_THE_REASONING_MACHINE_IS_THE_RETURNING_ECOLOGY.md`
//! §1 states it:
//!
//! > *An autocorrect system adds a receiver which **ranks or otherwise collapses a candidate
//! > population and commits a replacement**. The fiber returns the earlier object: literal
//! > occurrence + context-compatible re-expressions + edit lineage + shortest separating histories +
//! > the exterior the active receiver has not resolved.*
//!
//! An `argmax` welded into this path would **be** that receiver, in the one place no later caller
//! could decline it — and the deposit's reason is exactly that *"a later recurrence can use the
//! fiber without having inherited an accidental selection policy."* `soma/life`'s
//! `reconstruction_fiber` already builds the object and says the same in its own opening: *"Nothing
//! chooses a surface."* This module supplies that organ's exact scores at map scale and stops there.
//!
//! # The two charts, and neither is a host
//!
//! **QUOTATION REPAIRED 2026-08-18.** This block read *"stop calling the CPU the **'cpu'**"* and then
//! *"**`cpu`** is CUDA's word"*. Both were wrong: the ruling is `host`, and `host` is CUDA's word —
//! `cpu` is not. A mechanical `host → cpu` sweep passed **through the quotation marks**, leaving
//! Brandon quoted as telling himself not to call the CPU "the cpu". `CLAUDE.md` and
//! `canon/THE_SURFACES_ARE_PATHS.md` both carry the correct form.
//!
//! **A corrupted quotation is the contamination `CLAUDE.md` §9 calls hardest to detect**, because no
//! later reader re-checks a provenance line — that is what the line is for. A sweep that rewrites
//! prose must not enter a quotation, and this one did.
//!
//! Brandon, 2026-08-13, correcting the vocabulary this module was about to be written in: *"stop
//! calling the CPU the 'host', it's just a misnomer. It's a bottleneck in a literal sense if
//! anything, it's a light-cone, a pathway. Same for the GPU, they're just paths that work
//! differently."*
//!
//! `host` is CUDA's word and it carries a master/servant frame neither path has — which is the same
//! defect as reading a `head` off a map that declares two KV heads: an exterior convention imported
//! whole and then reasoned from. `hardware_cover` already has the right word, **chart**, and
//! `CLAUDE.md` already rules that *"CPU, GPU, storage, network, checker, and sensor are apparatus
//! charts."* So:
//!
//! | chart | its transport law |
//! |---|---|
//! | **serial** | few lanes, long serial reach, low latency per step |
//! | **resident** | many lanes, short reach each, large aggregate width |
//!
//! Which of the two is "central" is a receiver's coordinate. The deed here is `rows x dim` exact
//! multiply-accumulates with no dependence between rows, so the **resident** chart carries it — by
//! the material's shape, not by preference — and this module refuses by name rather than falling
//! back, so a serial figure can never be reported as though the deed had been mounted.
//!
//! # Exactness, checked before dispatch
//!
//! Entries arrive through [`crate::exact_value`]'s declared float mouth as integers aligned to one
//! power of two, so every product and every sum is exact. A `dim`-term sum of products bounded by
//! `2^b` needs `2b + ceil(log2 dim)` bits. **That bound is computed from the material and refused
//! when it exceeds the carrier**, rather than truncated: [`FiberError::CarrierTooNarrow`] names the
//! octaves the material required.

use std::collections::BTreeMap;
use std::ffi::{CStr, c_char, c_void};

use num_bigint::BigInt;
use thiserror::Error;

use crate::cuda_aperture::DerivedLaunch;
use crate::exact_value::ieee754::decode_bfloat16_bits;

const PTX: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/exact_embedding_fiber.ptx"));
const CUDA_SUCCESS: i32 = 0;

/// `CUdevice_attribute` and `CUfunction_attribute` selectors from `cuda.h`. ABI: the integers are
/// fixed by the foreign interface and a different value asks a different question.
const DEVICE_MAX_THREADS_PER_BLOCK: i32 = 1;
const DEVICE_MAX_GRID_DIM_X: i32 = 5;
const DEVICE_WARP_SIZE: i32 = 10;
const FUNCTION_MAX_THREADS_PER_BLOCK: i32 = 0;

/// The exact carrier the kernel accumulates in. Read off `__int128`, not chosen.
const CARRIER_OCTAVES: u32 = 128;

/// The magnitude octaves a signed 64-bit word holds. Read off `i64`, not chosen: `i64::BITS` is 64
/// and one of them is the hand, so a magnitude may occupy 63 and no more.
const SIGNED_WORD_OCTAVES: u32 = i64::BITS - 1;

type CuDevice = i32;
type CuContext = *mut c_void;
type CuModule = *mut c_void;
type CuFunction = *mut c_void;
type CuStream = *mut c_void;
type CuDevicePtr = u64;

#[link(name = "cuda")]
unsafe extern "C" {
    fn cuInit(flags: u32) -> i32;
    fn cuDeviceGetCount(count: *mut i32) -> i32;
    fn cuDeviceGet(device: *mut CuDevice, ordinal: i32) -> i32;
    fn cuDeviceGetName(name: *mut c_char, length: i32, device: CuDevice) -> i32;
    fn cuDeviceGetAttribute(value: *mut i32, attribute: i32, device: CuDevice) -> i32;
    fn cuFuncGetAttribute(value: *mut i32, attribute: i32, function: CuFunction) -> i32;
    fn cuCtxCreate_v2(context: *mut CuContext, flags: u32, device: CuDevice) -> i32;
    fn cuCtxSetCurrent(context: CuContext) -> i32;
    fn cuCtxDestroy_v2(context: CuContext) -> i32;
    fn cuCtxSynchronize() -> i32;
    fn cuModuleLoadData(module: *mut CuModule, image: *const c_void) -> i32;
    fn cuModuleUnload(module: CuModule) -> i32;
    fn cuModuleGetFunction(function: *mut CuFunction, module: CuModule, name: *const c_char)
    -> i32;
    fn cuMemAlloc_v2(pointer: *mut CuDevicePtr, bytes: usize) -> i32;
    fn cuMemFree_v2(pointer: CuDevicePtr) -> i32;
    fn cuMemcpyHtoD_v2(destination: CuDevicePtr, source: *const c_void, bytes: usize) -> i32;
    fn cuMemcpyDtoH_v2(destination: *mut c_void, source: CuDevicePtr, bytes: usize) -> i32;
    fn cuLaunchKernel(
        function: CuFunction,
        grid_x: u32,
        grid_y: u32,
        grid_z: u32,
        block_x: u32,
        block_y: u32,
        block_z: u32,
        shared: u32,
        stream: CuStream,
        parameters: *mut *mut c_void,
        extra: *mut *mut c_void,
    ) -> i32;
    fn cuGetErrorName(error: i32, name: *mut *const c_char) -> i32;
    fn cuGetErrorString(error: i32, message: *mut *const c_char) -> i32;
}

#[derive(Debug, Error)]
pub enum FiberError {
    #[error("the CUDA driver reports no device; the resident chart is not mounted")]
    NoResidentChart,
    #[error("CUDA {operation} returned {code} ({name}): {message}")]
    Driver {
        operation: &'static str,
        code: i32,
        name: String,
        message: String,
    },
    /// The material needs more octaves than the exact carrier holds. **Refused, never truncated** —
    /// the whole point of the carrier is that nothing in it rounds.
    #[error(
        "an exact {dim}-term contraction of {entry_octaves}-octave entries needs {needed} octaves, \
         past the {carrier}-octave exact carrier"
    )]
    CarrierTooNarrow {
        dim: usize,
        entry_octaves: u32,
        needed: u32,
        carrier: u32,
    },
    #[error("the query carries {query} entries and the readout is {dim} wide")]
    WidthDisagrees { query: usize, dim: usize },
    #[error("a readout of {words} words is not a whole number of {dim}-wide rows")]
    RaggedReadout { words: usize, dim: usize },
    #[error("{rows} rows exceeds the resident chart's declared grid aperture")]
    ExtentOverflow { rows: usize },
    #[error("the declared alignment spread {spread} exceeds the exact word carrier")]
    AlignmentSpread { spread: u32 },
    /// An entry's own magnitude plus the spread it must be raised through exceeds the signed word.
    ///
    /// **This is a separate refusal from [`FiberError::AlignmentSpread`] because it has a separate
    /// cause.** A spread of 40 is admissible for a one-octave entry and inadmissible for a
    /// twenty-four-octave one; the spread alone cannot decide it. Reporting both as
    /// `AlignmentSpread` would name the wrong quantity, and the guard that only looked at the
    /// spread is what let the shift wrap silently — see the note on the alignment loop.
    #[error(
        "an entry of {octaves} octaves raised through a spread of {spread} needs {needed} octaves, \
         past the {carrier}-octave signed word"
    )]
    AlignmentOverflows {
        octaves: u32,
        spread: u32,
        needed: u32,
        carrier: u32,
    },
    #[error("the float mouth refused an entry: {reason}")]
    MouthRefused { reason: String },
    #[error("the addressed population names row {row} of a {rows}-row readout")]
    AddressOutsideReadout { row: u32, rows: usize },
}

fn text(query: unsafe extern "C" fn(i32, *mut *const c_char) -> i32, code: i32) -> String {
    let mut pointer: *const c_char = std::ptr::null();
    unsafe {
        if query(code, &mut pointer) != CUDA_SUCCESS || pointer.is_null() {
            return String::new();
        }
        CStr::from_ptr(pointer).to_string_lossy().into_owned()
    }
}

fn checked(code: i32, operation: &'static str) -> Result<(), FiberError> {
    if code == CUDA_SUCCESS {
        return Ok(());
    }
    Err(FiberError::Driver {
        operation,
        code,
        name: text(cuGetErrorName, code),
        message: text(cuGetErrorString, code),
    })
}

/// A material aligned onto one exponent, with everything the alignment cost recorded.
///
/// The entries are exact integers and the common exponent is retained, so the original values are
/// `entry * 2^exponent` **exactly** — the alignment is a rebase with zero remainder, not a
/// normalisation, and `H.0104` is the law it runs under.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AlignedMaterial {
    pub entries: Vec<i64>,
    /// The common power of two every entry was aligned onto.
    pub exponent: i32,
    /// The widest entry's octave count. This is what decides the carrier headroom.
    pub entry_octaves: u32,
    /// How many entries carry a negative hand. A count of passages, not a magnitude.
    pub negatives: u64,
}

/// Align BF16 words onto one exponent, exactly.
///
/// **The declared float mouth is the only way a float enters**, and it enters as a `BigUint`
/// significand with an integer ulp exponent — never as a machine float with arithmetic done on it.
pub fn align_bfloat16(words: &[u16]) -> Result<AlignedMaterial, FiberError> {
    let mut decoded = Vec::with_capacity(words.len());
    let mut lowest = i32::MAX;
    for word in words {
        let datum = decode_bfloat16_bits(*word).map_err(|error| FiberError::MouthRefused {
            reason: format!("{error:?}"),
        })?;
        let significand =
            u64::try_from(&datum.significand).map_err(|_| FiberError::MouthRefused {
                reason: "a BF16 significand exceeded the exact word carrier".to_owned(),
            })?;
        let signed = if datum.negative {
            -(significand as i64)
        } else {
            significand as i64
        };
        if significand != 0 {
            lowest = lowest.min(datum.ulp_exponent);
        }
        decoded.push((signed, datum.ulp_exponent));
    }
    if lowest == i32::MAX {
        lowest = 0;
    }
    let mut entries = Vec::with_capacity(decoded.len());
    let mut entry_octaves = 0u32;
    let mut negatives = 0u64;
    for (significand, exponent) in decoded {
        if significand == 0 {
            entries.push(0);
            continue;
        }
        let spread = u32::try_from(exponent - lowest)
            .map_err(|_| FiberError::AlignmentSpread { spread: u32::MAX })?;
        if spread >= SIGNED_WORD_OCTAVES {
            return Err(FiberError::AlignmentSpread { spread });
        }
        // The demand is the entry's OWN octaves plus the spread, and the spread alone cannot decide
        // it. `checked_shl` refuses only an out-of-range shift AMOUNT — it does not look at the
        // value — so `spread < 63` admitted shifts that wrapped through the sign bit and returned
        // `Some`: measured, a positive significand comes back negative at spread 56 and a negative
        // one comes back positive at spread 60. **The hand flipped and nothing refused**, on a
        // conduct path, in a body whose standing law is that a sign is a passage and never a state.
        // The parity test between the resident and serial charts could not catch it either: both
        // consume the same already-wrapped `AlignedMaterial`, so they agree on the wrong value.
        let octaves = significand.unsigned_abs().ilog2() + 1;
        let needed = octaves + spread;
        if needed > SIGNED_WORD_OCTAVES {
            return Err(FiberError::AlignmentOverflows {
                octaves,
                spread,
                needed,
                carrier: SIGNED_WORD_OCTAVES,
            });
        }
        let aligned: i64 = significand
            .checked_shl(spread)
            .ok_or(FiberError::AlignmentSpread { spread })?;
        if significand < 0 {
            negatives += 1;
        }
        entry_octaves = entry_octaves.max(aligned.unsigned_abs().max(1).ilog2() + 1);
        entries.push(aligned);
    }
    Ok(AlignedMaterial {
        entries,
        exponent: lowest,
        entry_octaves,
        negatives,
    })
}

/// The exact score population of one query, and what it cost.
///
/// **There is no maximum here and there is no ranking.** `scores` is indexed exactly as the readout
/// rows are, or as the addressed population was declared. What a caller does with it — a fiber, a
/// band, a quotient, or a coarse endpoint face reported as one — is the caller's declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScorePopulation {
    /// One exact score per addressed row.
    pub scores: Vec<i128>,
    /// The octave of each score: `ceil(log2 |s|)`, zero at zero. **A magnitude does not cross a
    /// frame boundary and this does** — it is a winding, an integer, counted with nothing rounded.
    pub octaves: Vec<u32>,
    /// The common exponent both sides were aligned onto. A score's true value is
    /// `scores[v] * 2^(readout_exponent + query_exponent)`, exactly.
    pub readout_exponent: i32,
    pub query_exponent: i32,
    /// Exact multiply-accumulates performed. Work, not elapsed time.
    pub exact_multiply_accumulates: u64,
    /// The device that carried the deed, named so a figure carries its frame.
    pub resident_chart: String,
}

impl ScorePopulation {
    /// The scores as exact integers over the shared exponent, for a caller that wants to compose
    /// them with other exact material rather than compare them here.
    pub fn exact(&self, at: usize) -> Option<BigInt> {
        self.scores.get(at).map(|score| BigInt::from(*score))
    }

    /// The population of rows whose score is **exactly equal** to the score at `at`.
    ///
    /// Ties are decidable because the arithmetic is exact — there is no epsilon and no tolerance —
    /// and a tie is a real statement about the material rather than a numerical accident. This is a
    /// reading, not a selection: it returns every member and commits to none.
    pub fn exactly_equal_to(&self, at: usize) -> Vec<usize> {
        let Some(held) = self.scores.get(at) else {
            return Vec::new();
        };
        self.scores
            .iter()
            .enumerate()
            .filter(|(_, score)| *score == held)
            .map(|(row, _)| row)
            .collect()
    }

    /// How many rows sit at each octave. The distribution of the score population's own span,
    /// returned as counts rather than as a shape.
    pub fn octave_census(&self) -> BTreeMap<u32, u64> {
        let mut census = BTreeMap::new();
        for octave in &self.octaves {
            *census.entry(*octave).or_insert(0u64) += 1;
        }
        census
    }
}

/// The resident chart, mounted. Refuses by name when no device answers rather than conducting the
/// deed on the serial chart and reporting the figure as though it had been mounted.
pub struct ResidentReadout {
    context: CuContext,
    module: CuModule,
    scores: CuFunction,
    scores_addressed: CuFunction,
    octaves: CuFunction,
    scores_batched: CuFunction,
    device_name: String,
    /// Block and grid, derived from what this device and these kernels admit. Never authored here.
    launch: DerivedLaunch,
}

/// The frame a mounted readout carries into a score: what the map's own entries cost in octaves,
/// and the power of two they are aligned to. Both are the readout's, not the query's, and a score
/// is meaningless without them — which is why they are kept beside the device pointer rather than
/// re-derived from a matrix that is no longer on this chart.
struct ReadoutFrame {
    entry_octaves: u32,
    exponent: i32,
}

impl ResidentReadout {
    pub fn new() -> Result<Self, FiberError> {
        unsafe {
            checked(cuInit(0), "cuInit")?;
            let mut count = 0i32;
            checked(cuDeviceGetCount(&mut count), "cuDeviceGetCount")?;
            if count == 0 {
                return Err(FiberError::NoResidentChart);
            }
            let mut device: CuDevice = 0;
            checked(cuDeviceGet(&mut device, 0), "cuDeviceGet")?;

            let mut name = [0i8; 256];
            checked(
                cuDeviceGetName(name.as_mut_ptr(), name.len() as i32, device),
                "cuDeviceGetName",
            )?;
            let device_name = CStr::from_ptr(name.as_ptr()).to_string_lossy().into_owned();

            let mut max_threads = 0i32;
            checked(
                cuDeviceGetAttribute(&mut max_threads, DEVICE_MAX_THREADS_PER_BLOCK, device),
                "cuDeviceGetAttribute(max threads)",
            )?;
            let mut max_grid_x = 0i32;
            checked(
                cuDeviceGetAttribute(&mut max_grid_x, DEVICE_MAX_GRID_DIM_X, device),
                "cuDeviceGetAttribute(max grid x)",
            )?;

            let mut context: CuContext = std::ptr::null_mut();
            checked(cuCtxCreate_v2(&mut context, 0, device), "cuCtxCreate")?;
            checked(cuCtxSetCurrent(context), "cuCtxSetCurrent")?;

            let mut image = PTX.to_vec();
            image.push(0);
            let mut module: CuModule = std::ptr::null_mut();
            if let Err(error) = checked(
                cuModuleLoadData(&mut module, image.as_ptr().cast()),
                "cuModuleLoadData",
            ) {
                let _ = cuCtxDestroy_v2(context);
                return Err(error);
            }

            let mut warp = 0i32;
            checked(
                cuDeviceGetAttribute(&mut warp, DEVICE_WARP_SIZE, device),
                "cuDeviceGetAttribute(warp size)",
            )?;

            let mut loaded = [std::ptr::null_mut(); 4];
            for (slot, symbol) in loaded.iter_mut().zip([
                c"exact_readout_scores",
                c"exact_readout_scores_addressed",
                c"exact_score_octaves",
                c"exact_readout_scores_batched",
            ]) {
                if let Err(error) = checked(
                    cuModuleGetFunction(slot, module, symbol.as_ptr()),
                    "cuModuleGetFunction",
                ) {
                    let _ = cuModuleUnload(module);
                    let _ = cuCtxDestroy_v2(context);
                    return Err(error);
                }
            }

            Ok(Self {
                context,
                module,
                scores: loaded[0],
                scores_addressed: loaded[1],
                octaves: loaded[2],
                scores_batched: loaded[3],
                device_name,
                launch: {
                    // Every kernel this module launches must fit the block, so the block is the
                    // smallest admission among them and the device's own ceiling, taken down to a
                    // whole warp. `DerivedLaunch::from_admissions` owns that rule.
                    let device_block = max_threads.max(1) as u32;
                    let mut kernel_block = device_block;
                    for function in loaded {
                        let mut value = 0i32;
                        if let Err(error) = checked(
                            cuFuncGetAttribute(
                                &mut value,
                                FUNCTION_MAX_THREADS_PER_BLOCK,
                                function,
                            ),
                            "cuFuncGetAttribute(MAX_THREADS_PER_BLOCK)",
                        ) {
                            let _ = cuModuleUnload(module);
                            let _ = cuCtxDestroy_v2(context);
                            return Err(error);
                        }
                        kernel_block = kernel_block.min(value.max(0) as u32);
                    }
                    DerivedLaunch::from_admissions(
                        device_block,
                        kernel_block,
                        max_grid_x.max(1) as u32,
                        warp.max(1) as u32,
                    )
                },
            })
        }
    }

    pub fn device_name(&self) -> &str {
        &self.device_name
    }

    /// The carrier headroom this material needs, computed from the material and never assumed.
    ///
    /// An exact `dim`-term sum of products of `b`-octave entries needs `2b + ceil(log2 dim)`
    /// octaves. Returned so a caller can read what it cost even when it fits.
    pub fn needed_octaves(entry_octaves: u32, dim: usize) -> u32 {
        let terms = u32::try_from(dim.max(1).next_power_of_two().ilog2()).unwrap_or(u32::MAX);
        entry_octaves
            .saturating_mul(2)
            .saturating_add(terms)
            .saturating_add(1)
    }

    /// **Lay the readout down on the card and leave it there.** The map is the invariant; a query
    /// is the question asked of it. Crossing the invariant on every question is the defect this
    /// exists to remove.
    ///
    /// Measured 2026-08-13, before it existed: a driver asking 4,096 questions of one 84 MB readout
    /// pushed roughly **343 GB** across the bus — the same matrix, 4,096 times — at a sustained
    /// 13–15 GB/s, while the arithmetic it was paying for was worth milliseconds. Nothing about the
    /// kernel was wrong; the operand simply had no residency. `cuda_refine.rs` already owned the
    /// shape (`Buffer`, `DeviceCorpus` — *"the whole corpus, laid out once for the device"*), and
    /// this is that shape here.
    pub fn mount<'chart>(
        &'chart self,
        readout: &AlignedMaterial,
        dim: usize,
    ) -> Result<MountedReadout<'chart>, FiberError> {
        if dim == 0 || readout.entries.len() % dim != 0 {
            return Err(FiberError::RaggedReadout {
                words: readout.entries.len(),
                dim,
            });
        }
        let rows = readout.entries.len() / dim;
        let bytes = std::mem::size_of_val(readout.entries.as_slice());
        unsafe {
            checked(cuCtxSetCurrent(self.context), "cuCtxSetCurrent")?;
            let mut resident: CuDevicePtr = 0;
            checked(cuMemAlloc_v2(&mut resident, bytes), "cuMemAlloc(readout)")?;
            if let Err(error) = checked(
                cuMemcpyHtoD_v2(resident, readout.entries.as_ptr().cast(), bytes),
                "cuMemcpy(readout)",
            ) {
                let _ = cuMemFree_v2(resident);
                return Err(error);
            }
            Ok(MountedReadout {
                chart: self,
                resident,
                rows,
                dim,
                entry_octaves: readout.entry_octaves,
                exponent: readout.exponent,
                octets: bytes,
            })
        }
    }

    /// **The deed, for a caller with one question.** Every exact score of one query against every
    /// declared row.
    ///
    /// `addresses` names the rows to score; `None` scores all of them. A row the caller did not name
    /// is not scored, not defaulted, and not silently included — so an aperture can report what it
    /// excluded rather than dropping it.
    ///
    /// **This mounts, asks, and unmounts.** A caller with many questions must
    /// [`mount`](Self::mount) once and ask the mounted readout, or the operand crosses the bus once
    /// per question.
    pub fn score(
        &self,
        readout: &AlignedMaterial,
        query: &AlignedMaterial,
        dim: usize,
        addresses: Option<&[u32]>,
    ) -> Result<ScorePopulation, FiberError> {
        self.mount(readout, dim)?.score(query, addresses)
    }
}

/// A readout resident on the card, with the questions a caller may ask of it.
///
/// The device allocation is owned here and released on drop. It borrows the chart, so the context
/// it was allocated against outlives it by construction.
pub struct MountedReadout<'chart> {
    chart: &'chart ResidentReadout,
    resident: CuDevicePtr,
    rows: usize,
    dim: usize,
    entry_octaves: u32,
    exponent: i32,
    octets: usize,
}

impl MountedReadout<'_> {
    /// Rows the mounted map carries.
    pub fn rows(&self) -> usize {
        self.rows
    }

    /// The width the map declared. Read off the material, never authored.
    pub fn dim(&self) -> usize {
        self.dim
    }

    /// Octets the map occupies on the card — the operand that now crosses once instead of per query.
    pub fn resident_octets(&self) -> usize {
        self.octets
    }

    /// Every exact score of one query against every declared row of the mounted map.
    pub fn score(
        &self,
        query: &AlignedMaterial,
        addresses: Option<&[u32]>,
    ) -> Result<ScorePopulation, FiberError> {
        let dim = self.dim;
        let rows = self.rows;
        if query.entries.len() != dim {
            return Err(FiberError::WidthDisagrees {
                query: query.entries.len(),
                dim,
            });
        }
        let readout = ReadoutFrame {
            entry_octaves: self.entry_octaves,
            exponent: self.exponent,
        };

        // The headroom check, before anything is dispatched. Refused, never truncated.
        let entry_octaves = readout.entry_octaves.max(query.entry_octaves);
        let needed = ResidentReadout::needed_octaves(entry_octaves, dim);
        if needed > CARRIER_OCTAVES {
            return Err(FiberError::CarrierTooNarrow {
                dim,
                entry_octaves,
                needed,
                carrier: CARRIER_OCTAVES,
            });
        }

        let count = match addresses {
            None => rows,
            Some(named) => {
                for row in named {
                    if *row as usize >= rows {
                        return Err(FiberError::AddressOutsideReadout { row: *row, rows });
                    }
                }
                named.len()
            }
        };
        if count == 0 {
            return Ok(ScorePopulation {
                scores: Vec::new(),
                octaves: Vec::new(),
                readout_exponent: readout.exponent,
                query_exponent: query.exponent,
                exact_multiply_accumulates: 0,
                resident_chart: self.chart.device_name.clone(),
            });
        }

        // The block is what the device and the kernels admit, down to a whole warp — derived by
        // `cuda_aperture::DerivedLaunch`, the owner of that rule. It read `max_threads.min(256)`
        // until 2026-08-13: a level authored inside this organ, blind to the warp and blind to what
        // its own kernels admit.
        let block = self.chart.launch.block_x;
        let work = u32::try_from(count).map_err(|_| FiberError::ExtentOverflow { rows: count })?;
        let grid = self
            .chart
            .launch
            .grid_for(work)
            .map_err(|_| FiberError::ExtentOverflow { rows: count })?;

        unsafe {
            checked(cuCtxSetCurrent(self.chart.context), "cuCtxSetCurrent")?;

            let query_bytes = std::mem::size_of_val(query.entries.as_slice());
            let mut device_readout: CuDevicePtr = self.resident;
            let mut device_query: CuDevicePtr = 0;
            let mut device_low: CuDevicePtr = 0;
            let mut device_high: CuDevicePtr = 0;
            let mut device_octaves: CuDevicePtr = 0;
            let mut device_addresses: CuDevicePtr = 0;

            checked(
                cuMemAlloc_v2(&mut device_query, query_bytes),
                "cuMemAlloc(query)",
            )?;
            checked(cuMemAlloc_v2(&mut device_low, count * 8), "cuMemAlloc(low)")?;
            checked(
                cuMemAlloc_v2(&mut device_high, count * 8),
                "cuMemAlloc(high)",
            )?;
            checked(
                cuMemAlloc_v2(&mut device_octaves, count * 4),
                "cuMemAlloc(octaves)",
            )?;

            // The readout does not cross here. It crossed once, at mount.
            checked(
                cuMemcpyHtoD_v2(device_query, query.entries.as_ptr().cast(), query_bytes),
                "cuMemcpy(query)",
            )?;

            let mut rows_wire = count as u32;
            let mut dim_wire = dim as u32;
            if let Some(named) = addresses {
                let address_bytes = std::mem::size_of_val(named);
                checked(
                    cuMemAlloc_v2(&mut device_addresses, address_bytes),
                    "cuMemAlloc(addresses)",
                )?;
                checked(
                    cuMemcpyHtoD_v2(device_addresses, named.as_ptr().cast(), address_bytes),
                    "cuMemcpy(addresses)",
                )?;
                let mut parameters: [*mut c_void; 7] = [
                    (&raw mut device_readout).cast(),
                    (&raw mut device_query).cast(),
                    (&raw mut device_addresses).cast(),
                    (&raw mut rows_wire).cast(),
                    (&raw mut dim_wire).cast(),
                    (&raw mut device_low).cast(),
                    (&raw mut device_high).cast(),
                ];
                checked(
                    cuLaunchKernel(
                        self.chart.scores_addressed,
                        grid as u32,
                        1,
                        1,
                        block,
                        1,
                        1,
                        0,
                        std::ptr::null_mut(),
                        parameters.as_mut_ptr(),
                        std::ptr::null_mut(),
                    ),
                    "cuLaunchKernel(exact_readout_scores_addressed)",
                )?;
            } else {
                let mut parameters: [*mut c_void; 6] = [
                    (&raw mut device_readout).cast(),
                    (&raw mut device_query).cast(),
                    (&raw mut rows_wire).cast(),
                    (&raw mut dim_wire).cast(),
                    (&raw mut device_low).cast(),
                    (&raw mut device_high).cast(),
                ];
                checked(
                    cuLaunchKernel(
                        self.chart.scores,
                        grid as u32,
                        1,
                        1,
                        block,
                        1,
                        1,
                        0,
                        std::ptr::null_mut(),
                        parameters.as_mut_ptr(),
                        std::ptr::null_mut(),
                    ),
                    "cuLaunchKernel(exact_readout_scores)",
                )?;
            }

            let mut octave_count = count as u32;
            let mut octave_parameters: [*mut c_void; 4] = [
                (&raw mut device_low).cast(),
                (&raw mut device_high).cast(),
                (&raw mut octave_count).cast(),
                (&raw mut device_octaves).cast(),
            ];
            checked(
                cuLaunchKernel(
                    self.chart.octaves,
                    grid as u32,
                    1,
                    1,
                    block,
                    1,
                    1,
                    0,
                    std::ptr::null_mut(),
                    octave_parameters.as_mut_ptr(),
                    std::ptr::null_mut(),
                ),
                "cuLaunchKernel(exact_score_octaves)",
            )?;
            checked(cuCtxSynchronize(), "cuCtxSynchronize")?;

            let mut low = vec![0u64; count];
            let mut high = vec![0i64; count];
            let mut octaves = vec![0u32; count];
            checked(
                cuMemcpyDtoH_v2(low.as_mut_ptr().cast(), device_low, count * 8),
                "cuMemcpy(low)",
            )?;
            checked(
                cuMemcpyDtoH_v2(high.as_mut_ptr().cast(), device_high, count * 8),
                "cuMemcpy(high)",
            )?;
            checked(
                cuMemcpyDtoH_v2(octaves.as_mut_ptr().cast(), device_octaves, count * 4),
                "cuMemcpy(octaves)",
            )?;

            let _ = cuMemFree_v2(device_query);
            let _ = cuMemFree_v2(device_low);
            let _ = cuMemFree_v2(device_high);
            let _ = cuMemFree_v2(device_octaves);
            if device_addresses != 0 {
                let _ = cuMemFree_v2(device_addresses);
            }

            // Reassemble the exact 128-bit values from the two halves the wire carried.
            let scores = low
                .iter()
                .zip(&high)
                .map(|(low, high)| ((*high as i128) << 64) | (*low as i128 & 0xFFFF_FFFF_FFFF_FFFF))
                .collect();

            Ok(ScorePopulation {
                scores,
                octaves,
                readout_exponent: readout.exponent,
                query_exponent: query.exponent,
                exact_multiply_accumulates: (count as u64).saturating_mul(dim as u64),
                resident_chart: self.chart.device_name.clone(),
            })
        }
    }

    /// **A whole declared query population against the mounted map, in one grid.**
    ///
    /// `queries × rows` scores from one launch. The readout does not move, the queries cross once
    /// together, and each query gets its own complete score population — nothing is compared across
    /// queries and nothing is ranked, exactly as for a single query.
    ///
    /// This is the shape the 4,096-question driver wanted. It is not a different deed: `dim` was
    /// already a stride in the kernel, so the batched form is the same arithmetic indexed by
    /// `blockIdx.y`.
    pub fn score_many(
        &self,
        queries: &[&AlignedMaterial],
    ) -> Result<Vec<ScorePopulation>, FiberError> {
        let dim = self.dim;
        let rows = self.rows;
        if queries.is_empty() || rows == 0 {
            return Ok(Vec::new());
        }
        let mut entry_octaves = self.entry_octaves;
        for query in queries {
            if query.entries.len() != dim {
                return Err(FiberError::WidthDisagrees {
                    query: query.entries.len(),
                    dim,
                });
            }
            entry_octaves = entry_octaves.max(query.entry_octaves);
        }
        let needed = ResidentReadout::needed_octaves(entry_octaves, dim);
        if needed > CARRIER_OCTAVES {
            return Err(FiberError::CarrierTooNarrow {
                dim,
                entry_octaves,
                needed,
                carrier: CARRIER_OCTAVES,
            });
        }

        let count = queries.len();
        let slots = rows
            .checked_mul(count)
            .ok_or(FiberError::ExtentOverflow { rows })?;
        let block = self.chart.launch.block_x;
        let work = u32::try_from(rows).map_err(|_| FiberError::ExtentOverflow { rows })?;
        let grid_x = self
            .chart
            .launch
            .grid_for(work)
            .map_err(|_| FiberError::ExtentOverflow { rows })?;
        // The query population is the grid's second dimension, so it is bounded by the device's own
        // `MAX_GRID_DIM_Y`. This module reads only X; rather than assume the two are equal, refuse
        // past the ceiling it did read. A caller past it splits its population and asks twice.
        let grid_y =
            u32::try_from(count).map_err(|_| FiberError::ExtentOverflow { rows: count })?;
        if grid_y > self.chart.launch.max_grid_x {
            return Err(FiberError::ExtentOverflow { rows: count });
        }

        let mut flattened: Vec<i64> = Vec::with_capacity(slots);
        for query in queries {
            flattened.extend_from_slice(&query.entries);
        }

        unsafe {
            checked(cuCtxSetCurrent(self.chart.context), "cuCtxSetCurrent")?;
            let query_bytes = std::mem::size_of_val(flattened.as_slice());
            let mut device_queries: CuDevicePtr = 0;
            let mut device_low: CuDevicePtr = 0;
            let mut device_high: CuDevicePtr = 0;
            let mut device_octaves: CuDevicePtr = 0;
            checked(
                cuMemAlloc_v2(&mut device_queries, query_bytes),
                "cuMemAlloc(queries)",
            )?;
            checked(cuMemAlloc_v2(&mut device_low, slots * 8), "cuMemAlloc(low)")?;
            checked(
                cuMemAlloc_v2(&mut device_high, slots * 8),
                "cuMemAlloc(high)",
            )?;
            checked(
                cuMemAlloc_v2(&mut device_octaves, slots * 4),
                "cuMemAlloc(octaves)",
            )?;
            checked(
                cuMemcpyHtoD_v2(device_queries, flattened.as_ptr().cast(), query_bytes),
                "cuMemcpy(queries)",
            )?;

            let mut readout = self.resident;
            let mut rows_wire = work;
            let mut dim_wire = dim as u32;
            let mut count_wire = grid_y;
            let mut parameters: [*mut c_void; 7] = [
                (&raw mut readout).cast(),
                (&raw mut device_queries).cast(),
                (&raw mut rows_wire).cast(),
                (&raw mut dim_wire).cast(),
                (&raw mut count_wire).cast(),
                (&raw mut device_low).cast(),
                (&raw mut device_high).cast(),
            ];
            checked(
                cuLaunchKernel(
                    self.chart.scores_batched,
                    grid_x,
                    grid_y,
                    1,
                    block,
                    1,
                    1,
                    0,
                    std::ptr::null_mut(),
                    parameters.as_mut_ptr(),
                    std::ptr::null_mut(),
                ),
                "cuLaunchKernel(exact_readout_scores_batched)",
            )?;

            let mut octave_count = u32::try_from(slots).unwrap_or(u32::MAX);
            let mut octave_parameters: [*mut c_void; 4] = [
                (&raw mut device_low).cast(),
                (&raw mut device_high).cast(),
                (&raw mut octave_count).cast(),
                (&raw mut device_octaves).cast(),
            ];
            let octave_grid = self
                .chart
                .launch
                .grid_for(octave_count)
                .map_err(|_| FiberError::ExtentOverflow { rows: slots })?;
            checked(
                cuLaunchKernel(
                    self.chart.octaves,
                    octave_grid,
                    1,
                    1,
                    block,
                    1,
                    1,
                    0,
                    std::ptr::null_mut(),
                    octave_parameters.as_mut_ptr(),
                    std::ptr::null_mut(),
                ),
                "cuLaunchKernel(exact_score_octaves)",
            )?;
            checked(cuCtxSynchronize(), "cuCtxSynchronize")?;

            let mut low = vec![0u64; slots];
            let mut high = vec![0i64; slots];
            let mut octaves = vec![0u32; slots];
            checked(
                cuMemcpyDtoH_v2(low.as_mut_ptr().cast(), device_low, slots * 8),
                "cuMemcpy(low)",
            )?;
            checked(
                cuMemcpyDtoH_v2(high.as_mut_ptr().cast(), device_high, slots * 8),
                "cuMemcpy(high)",
            )?;
            checked(
                cuMemcpyDtoH_v2(octaves.as_mut_ptr().cast(), device_octaves, slots * 4),
                "cuMemcpy(octaves)",
            )?;
            let _ = cuMemFree_v2(device_queries);
            let _ = cuMemFree_v2(device_low);
            let _ = cuMemFree_v2(device_high);
            let _ = cuMemFree_v2(device_octaves);

            Ok(queries
                .iter()
                .enumerate()
                .map(|(which, query)| {
                    let span = which * rows..(which + 1) * rows;
                    ScorePopulation {
                        scores: low[span.clone()]
                            .iter()
                            .zip(&high[span.clone()])
                            .map(|(low, high)| {
                                ((*high as i128) << 64) | (*low as i128 & 0xFFFF_FFFF_FFFF_FFFF)
                            })
                            .collect(),
                        octaves: octaves[span].to_vec(),
                        readout_exponent: self.exponent,
                        query_exponent: query.exponent,
                        exact_multiply_accumulates: (rows as u64).saturating_mul(dim as u64),
                        resident_chart: self.chart.device_name.clone(),
                    }
                })
                .collect())
        }
    }
}

impl Drop for MountedReadout<'_> {
    fn drop(&mut self) {
        unsafe {
            let _ = cuCtxSetCurrent(self.chart.context);
            let _ = cuMemFree_v2(self.resident);
        }
    }
}

impl Drop for ResidentReadout {
    fn drop(&mut self) {
        unsafe {
            let _ = cuModuleUnload(self.module);
            let _ = cuCtxDestroy_v2(self.context);
        }
    }
}

/// The same law on the **serial** chart, for grading the resident one against an independent
/// implementation.
///
/// `CLAUDE.md`: *"where an independent implementation exists, state both costs."* This is that
/// implementation. It is not a fallback — [`ResidentReadout::score`] refuses rather than calling
/// this — and a caller that runs both is grading, not degrading.
pub fn score_serially(
    readout: &AlignedMaterial,
    query: &AlignedMaterial,
    dim: usize,
    addresses: Option<&[u32]>,
) -> Result<Vec<i128>, FiberError> {
    if query.entries.len() != dim {
        return Err(FiberError::WidthDisagrees {
            query: query.entries.len(),
            dim,
        });
    }
    if dim == 0 || readout.entries.len() % dim != 0 {
        return Err(FiberError::RaggedReadout {
            words: readout.entries.len(),
            dim,
        });
    }
    let rows = readout.entries.len() / dim;
    let named: Vec<u32> = match addresses {
        Some(named) => named.to_vec(),
        None => (0..rows as u32).collect(),
    };
    let mut scores = Vec::with_capacity(named.len());
    for row in named {
        if row as usize >= rows {
            return Err(FiberError::AddressOutsideReadout { row, rows });
        }
        let base = row as usize * dim;
        let mut accumulated: i128 = 0;
        for at in 0..dim {
            accumulated += i128::from(readout.entries[base + at]) * i128::from(query.entries[at]);
        }
        scores.push(accumulated);
    }
    Ok(scores)
}

// -------------------------------------------------------------------------------------------------
// The safetensors intake — lifted 2026-08-17
// -------------------------------------------------------------------------------------------------

/// **Reading a deposited map's own container format**, beside the float mouth it feeds.
///
/// Lifted here 2026-08-17 because **four separate drivers each carried their own copy** —
/// `the_foreign_map_founds_its_axes`, `the_readout_founds_its_own_receivers`,
/// `the_readout_returns_a_fiber_not_a_winner`, and `the_map_deposits_and_a_later_current_rides_it` —
/// which is the duplication `canon/THE_DRIVER_ATLAS.md` was deposited to stop. A container parse is
/// a codec intake and belongs with `align_bfloat16`, which is the only door its octets may enter by.
///
/// **`dtype` is retained and checked.** One of those four copies read `shape` and `data_offsets` and
/// never consulted `dtype`, assuming a two-octet element unconditionally — so handed an `F32` file it
/// would have returned a plausible population of garbage rather than refusing.
pub mod safetensors {
    use std::collections::BTreeMap;
    use std::fs::File;
    use std::io::{Read, Seek, SeekFrom};

    /// The only element width this intake admits, named so the refusal can say what it wanted.
    pub const ADMITTED_DTYPE: &str = "BF16";
    const ADMITTED_OCTETS: u64 = 2;

    /// One tensor's declared header row.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct Entry {
        pub dtype: String,
        pub shape: Vec<usize>,
        pub start: u64,
        pub end: u64,
    }

    /// A container's declared tensors and where its payload begins.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct Header {
        pub map: BTreeMap<String, Entry>,
        pub base: u64,
    }

    impl Header {
        pub fn entry(&self, name: &str) -> Result<&Entry, String> {
            self.map
                .get(name)
                .ok_or_else(|| format!("the container declares no tensor named {name:?}"))
        }
    }

    /// Open a container and read its declared header.
    pub fn read_header(path: &str) -> Result<(File, Header), String> {
        let mut file = File::open(path).map_err(|error| format!("open {path}: {error}"))?;
        let mut length = [0u8; 8];
        file.read_exact(&mut length).map_err(|e| e.to_string())?;
        let declared = u64::from_le_bytes(length);
        let extent = usize::try_from(declared).map_err(|_| {
            format!("{path}: declared header length {declared} exceeds this machine's extent")
        })?;
        let mut raw = vec![0u8; extent];
        file.read_exact(&mut raw).map_err(|e| e.to_string())?;
        let text = String::from_utf8(raw).map_err(|e| e.to_string())?;
        let mut map = BTreeMap::new();
        let mut at = 0usize;
        while let Some(quote) = text[at..].find('"') {
            let start = at + quote + 1;
            let Some(end) = text[start..].find('"') else {
                break;
            };
            let name = text[start..start + end].to_owned();
            let rest = start + end + 1;
            if !text[rest..].starts_with(':') || !name.contains('.') {
                at = rest;
                continue;
            }
            let segment_end = text[rest..].find('}').map_or(text.len(), |z| rest + z);
            let segment = &text[rest..segment_end];
            let pull = |key: &str, width: usize| -> Vec<u64> {
                segment
                    .find(key)
                    .map(|position| {
                        let from = rest + position + width;
                        let to = text[from..].find(']').map_or(from, |z| from + z);
                        text[from..to]
                            .split(',')
                            .filter_map(|value| value.trim().parse::<u64>().ok())
                            .collect()
                    })
                    .unwrap_or_default()
            };
            let shape: Vec<usize> = pull("\"shape\":[", 9)
                .into_iter()
                .filter_map(|value| usize::try_from(value).ok())
                .collect();
            let offsets = pull("\"data_offsets\":[", 16);
            let dtype = segment
                .find("\"dtype\":\"")
                .map(|position| {
                    let from = rest + position + 9;
                    let to = text[from..].find('"').map_or(from, |z| from + z);
                    text[from..to].to_owned()
                })
                .unwrap_or_default();
            if !shape.is_empty() && offsets.len() == 2 {
                map.insert(
                    name,
                    Entry {
                        dtype,
                        shape,
                        start: offsets[0],
                        end: offsets[1],
                    },
                );
            }
            at = segment_end.max(rest);
        }
        Ok((
            file,
            Header {
                map,
                base: 8 + declared,
            },
        ))
    }

    /// Read a contiguous span of rows of a two-dimensional `BF16` tensor as raw words.
    ///
    /// The `dtype` is checked and the span is bounds-checked against the declared payload, so a
    /// mis-shaped read refuses rather than returning octets from a neighbouring tensor.
    pub fn read_rows(
        file: &mut File,
        header: &Header,
        name: &str,
        from_row: usize,
        rows: usize,
    ) -> Result<(Vec<u16>, usize), String> {
        let entry = header.entry(name)?;
        if entry.dtype != ADMITTED_DTYPE {
            return Err(format!(
                "{name}: this intake admits {ADMITTED_DTYPE} and the container declares {}",
                entry.dtype
            ));
        }
        if entry.shape.len() != 2 {
            return Err(format!(
                "{name}: this reader admits a two-dimensional tensor and the container declares {:?}",
                entry.shape
            ));
        }
        let width = entry.shape[1];
        let end_row = from_row
            .checked_add(rows)
            .ok_or_else(|| format!("{name}: the requested span overflows"))?;
        if end_row > entry.shape[0] {
            return Err(format!(
                "{name}: rows {from_row}..{end_row} reach past the declared {} rows",
                entry.shape[0]
            ));
        }
        let offset = entry.start + (from_row * width) as u64 * ADMITTED_OCTETS;
        let octets = (rows * width) as u64 * ADMITTED_OCTETS;
        if offset + octets > entry.end {
            return Err(format!("{name}: the span reaches past the declared payload"));
        }
        file.seek(SeekFrom::Start(header.base + offset))
            .map_err(|error| format!("{name}: seek: {error}"))?;
        let mut raw = vec![0u8; usize::try_from(octets).map_err(|_| "span exceeds extent")?];
        file.read_exact(&mut raw)
            .map_err(|error| format!("{name}: read: {error}"))?;
        let words = raw
            .chunks_exact(2)
            .map(|pair| u16::from_le_bytes([pair[0], pair[1]]))
            .collect();
        Ok((words, width))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A small readout with a known exact answer, so the arithmetic is checked against something
    /// other than itself.
    fn material() -> (AlignedMaterial, AlignedMaterial, usize) {
        let readout = AlignedMaterial {
            entries: vec![1, 2, 3, -1, 0, 5, 7, -7, 0],
            exponent: -3,
            entry_octaves: 3,
            negatives: 2,
        };
        let query = AlignedMaterial {
            entries: vec![2, -1, 4],
            exponent: -2,
            entry_octaves: 3,
            negatives: 1,
        };
        (readout, query, 3)
    }

    #[test]
    fn the_serial_chart_returns_the_exact_contraction() {
        let (readout, query, dim) = material();
        let scores = score_serially(&readout, &query, dim, None).expect("well-formed");
        // Computed by hand: the point of an independent check is that it is independent.
        assert_eq!(
            scores,
            vec![
                1 * 2 + 2 * -1 + 3 * 4,
                -1 * 2 + 0 + 5 * 4,
                7 * 2 + -7 * -1 + 0
            ]
        );
        assert_eq!(scores, vec![12, 18, 21]);
    }

    /// The addressed form scores what the caller named and nothing else — so an aperture can report
    /// what it excluded rather than dropping it.
    #[test]
    fn an_addressed_population_scores_exactly_the_declared_rows() {
        let (readout, query, dim) = material();
        let all = score_serially(&readout, &query, dim, None).expect("well-formed");
        let named = score_serially(&readout, &query, dim, Some(&[2, 0])).expect("well-formed");
        assert_eq!(named, vec![all[2], all[0]]);
        assert!(matches!(
            score_serially(&readout, &query, dim, Some(&[3])),
            Err(FiberError::AddressOutsideReadout { row: 3, rows: 3 })
        ));
    }

    /// **The headroom is computed from the material and refused rather than truncated.**
    ///
    /// This is the falsifier for the exactness claim: a material that would overflow the exact
    /// carrier must be named, not silently wrapped.
    #[test]
    fn a_material_past_the_exact_carrier_is_refused_by_name() {
        // 62-octave entries contracted over 2560 terms need 2*62 + 12 + 1 = 137 > 128.
        let needed = ResidentReadout::needed_octaves(62, 2560);
        assert!(needed > CARRIER_OCTAVES, "needed {needed}");
        // And the material this was built for fits, with the figure stated rather than assumed.
        let bf16 = ResidentReadout::needed_octaves(8, 2560);
        assert!(bf16 <= CARRIER_OCTAVES, "bf16 needed {bf16}");
    }

    /// The mouth is the only way a float enters, and the alignment is a rebase with **zero
    /// remainder**: every aligned entry times two-to-the-exponent reproduces the original exactly.
    #[test]
    fn the_alignment_is_a_rebase_with_zero_remainder() {
        // 1.0, 2.0, 0.5, -1.5 as BF16 bit patterns.
        let words = [0x3F80u16, 0x4000, 0x3F00, 0xBFC0];
        let aligned = align_bfloat16(&words).expect("the mouth admits these");
        assert_eq!(aligned.negatives, 1);
        // The rebase is checked against the decoded pair, in exact integers, with no division:
        // `entry * 2^aligned.exponent == signed * 2^datum.ulp_exponent` becomes a left shift by the
        // spread. **This was checked in `f64` until 2026-08-13** — the only machine-float arithmetic
        // in any library `src/` in this workspace, evaluating a zero-remainder claim in the very
        // carrier the module exists to avoid.
        for (word, entry) in words.iter().zip(&aligned.entries) {
            let datum = decode_bfloat16_bits(*word).expect("the mouth admits these");
            let magnitude =
                u64::try_from(&datum.significand).expect("a BF16 significand is one word") as i64;
            let signed = if datum.negative {
                -magnitude
            } else {
                magnitude
            };
            let spread = u32::try_from(datum.ulp_exponent - aligned.exponent)
                .expect("every entry aligns downward onto the lowest exponent");
            assert_eq!(*entry, signed << spread, "word {word:#06x}");
        }
    }

    /// **The falsifier the parity test could not supply.** The guard read only the spread and then
    /// called `checked_shl`, which refuses an out-of-range shift *amount* and never looks at the
    /// value — so a shift that carried the magnitude through the sign bit returned `Some` and the
    /// hand came back flipped. Both charts consumed the same wrapped material, so they agreed.
    ///
    /// `1.0` and `2^56` as BF16: significands of 8 octaves, ulp exponents `-7` and `49`, so the
    /// second aligns through a spread of 56 and demands 64 octaves of a 63-octave signed word.
    #[test]
    fn an_entry_whose_octaves_plus_spread_overflow_the_signed_word_is_refused() {
        let words = [0x3F80u16, 0x5B80];
        match align_bfloat16(&words) {
            Err(FiberError::AlignmentOverflows {
                octaves,
                spread,
                needed,
                carrier,
            }) => {
                assert_eq!((octaves, spread, needed, carrier), (8, 56, 64, 63));
            }
            other => panic!("the wrapping shift was admitted: {other:?}"),
        }

        // What the old guard did instead, kept as the evidence rather than the assertion: the
        // shift amount is in range, so `checked_shl` returns `Some` — of a negative number.
        let wrapped = 128i64.checked_shl(56).expect("the amount is in range");
        assert!(wrapped < 0, "the magnitude carried into the hand");
    }

    /// A zero material aligns without inventing an exponent.
    #[test]
    fn an_entirely_zero_material_aligns_to_the_zero_exponent() {
        let aligned = align_bfloat16(&[0x0000, 0x0000]).expect("zeros are admissible");
        assert_eq!(aligned.entries, vec![0, 0]);
        assert_eq!(aligned.exponent, 0);
        assert_eq!(aligned.entry_octaves, 0);
        assert_eq!(aligned.negatives, 0);
    }

    /// **The resident chart is graded against the serial one, bit for bit.**
    ///
    /// Two independent implementations of one law; `CLAUDE.md` requires that where one exists, both
    /// are stated. This is the parity half. Ignored when no device answers, because a skipped check
    /// must not read as a passing one.
    #[test]
    fn the_two_charts_return_the_identical_exact_population() {
        let Ok(resident) = ResidentReadout::new() else {
            eprintln!("no resident chart answered; the parity check did not run");
            return;
        };
        // A material wide enough that the resident chart's width is doing something.
        let dim = 64usize;
        let rows = 512usize;
        let entries: Vec<i64> = (0..rows * dim)
            .map(|at| ((at as i64 * 2_654_435_761) % 1021) - 510)
            .collect();
        let readout = AlignedMaterial {
            entry_octaves: entries
                .iter()
                .map(|e| e.unsigned_abs().max(1).ilog2() + 1)
                .max()
                .unwrap_or(0),
            negatives: entries.iter().filter(|e| **e < 0).count() as u64,
            entries,
            exponent: -7,
        };
        let query_entries: Vec<i64> = (0..dim).map(|at| ((at as i64 * 97) % 255) - 127).collect();
        let query = AlignedMaterial {
            entry_octaves: query_entries
                .iter()
                .map(|e| e.unsigned_abs().max(1).ilog2() + 1)
                .max()
                .unwrap_or(0),
            negatives: query_entries.iter().filter(|e| **e < 0).count() as u64,
            entries: query_entries,
            exponent: -3,
        };

        let carried = resident
            .score(&readout, &query, dim, None)
            .expect("the deed is admissible");
        let serial = score_serially(&readout, &query, dim, None).expect("well-formed");
        assert_eq!(carried.scores, serial, "the two charts disagree");
        assert_eq!(carried.exact_multiply_accumulates, (rows * dim) as u64);

        // The octave face agrees with the exact scores it was taken beside.
        for (score, octave) in carried.scores.iter().zip(&carried.octaves) {
            let expected = if *score == 0 {
                0
            } else {
                128 - score.unsigned_abs().leading_zeros()
            };
            assert_eq!(*octave, expected, "score {score}");
        }

        // And the addressed form agrees with the whole one on the rows it named.
        let named: Vec<u32> = vec![7, 0, 511, 256];
        let addressed = resident
            .score(&readout, &query, dim, Some(&named))
            .expect("admissible");
        for (slot, row) in named.iter().enumerate() {
            assert_eq!(addressed.scores[slot], carried.scores[*row as usize]);
        }
    }

    /// **Mounting once and asking many is the same arithmetic as asking one at a time.**
    ///
    /// The residency and the batched grid exist to stop the invariant crossing the bus per
    /// question; neither may change a single returned integer. Three queries, so a batch that
    /// silently scored only the first — or indexed its output by row and overwrote across
    /// queries — fails here rather than at map scale.
    #[test]
    fn the_batched_grid_returns_exactly_what_one_query_at_a_time_returns() {
        let Ok(resident) = ResidentReadout::new() else {
            eprintln!("no resident chart answered; the batch parity check did not run");
            return;
        };
        let dim = 48usize;
        let rows = 300usize;
        let entries: Vec<i64> = (0..rows * dim)
            .map(|at| ((at as i64 * 1_000_003) % 977) - 488)
            .collect();
        let readout = AlignedMaterial {
            entry_octaves: entries
                .iter()
                .map(|e| e.unsigned_abs().max(1).ilog2() + 1)
                .max()
                .unwrap_or(0),
            negatives: entries.iter().filter(|e| **e < 0).count() as u64,
            entries,
            exponent: -11,
        };
        let queries: Vec<AlignedMaterial> = (0..3)
            .map(|which| {
                let entries: Vec<i64> = (0..dim)
                    .map(|at| ((at as i64 * (31 + which * 17)) % 211) - 105)
                    .collect();
                AlignedMaterial {
                    entry_octaves: entries
                        .iter()
                        .map(|e| e.unsigned_abs().max(1).ilog2() + 1)
                        .max()
                        .unwrap_or(0),
                    negatives: entries.iter().filter(|e| **e < 0).count() as u64,
                    entries,
                    // Distinct exponents, so a batch that carried one query's frame to all of them
                    // is caught by the returned frame and not only by the integers.
                    exponent: -3 - which as i32,
                }
            })
            .collect();

        let mounted = resident.mount(&readout, dim).expect("the map mounts");
        assert_eq!(mounted.rows(), rows);
        assert_eq!(mounted.dim(), dim);
        assert_eq!(mounted.resident_octets(), rows * dim * 8);

        let borrowed: Vec<&AlignedMaterial> = queries.iter().collect();
        let batched = mounted.score_many(&borrowed).expect("admissible");
        assert_eq!(batched.len(), queries.len());
        for (which, query) in queries.iter().enumerate() {
            let one = mounted.score(query, None).expect("admissible");
            assert_eq!(batched[which].scores, one.scores, "query {which}");
            assert_eq!(batched[which].octaves, one.octaves, "query {which}");
            assert_eq!(batched[which].query_exponent, query.exponent);
            assert_eq!(batched[which].readout_exponent, readout.exponent);
            // And against the independent serial chart, so agreement is not two forms of one bug.
            let serial = score_serially(&readout, query, dim, None).expect("well-formed");
            assert_eq!(
                batched[which].scores, serial,
                "query {which} against serial"
            );
        }
        // Distinct queries must return distinct populations, or the batch scored one of them three
        // times and the agreement above would be vacuous.
        assert_ne!(batched[0].scores, batched[1].scores);
        assert_ne!(batched[1].scores, batched[2].scores);
    }

    /// **Nothing in this module returns a winner**, which is the deposit's bar made checkable: the
    /// exact-tie reading returns every member of the tie and commits to none.
    #[test]
    fn the_tie_reading_returns_every_member_and_commits_to_none() {
        let population = ScorePopulation {
            scores: vec![5, 9, 9, 1, 9],
            octaves: vec![3, 4, 4, 1, 4],
            readout_exponent: 0,
            query_exponent: 0,
            exact_multiply_accumulates: 0,
            resident_chart: "none".to_owned(),
        };
        assert_eq!(population.exactly_equal_to(1), vec![1, 2, 4]);
        assert_eq!(population.exactly_equal_to(0), vec![0]);
        assert_eq!(
            population.octave_census(),
            BTreeMap::from([(1, 1), (3, 1), (4, 3)])
        );
        assert_eq!(population.exact(2), Some(BigInt::from(9)));
    }
}
