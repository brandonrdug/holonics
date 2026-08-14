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

use crate::exact_value::ieee754::decode_bfloat16_bits;

const PTX: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/exact_embedding_fiber.ptx"));
const CUDA_SUCCESS: i32 = 0;

const DEVICE_MAX_THREADS_PER_BLOCK: i32 = 1;
const DEVICE_MAX_GRID_DIM_X: i32 = 5;

/// The exact carrier the kernel accumulates in. Read off `__int128`, not chosen.
const CARRIER_OCTAVES: u32 = 128;

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
        let datum = decode_bfloat16_bits(*word)
            .map_err(|error| FiberError::MouthRefused { reason: format!("{error:?}") })?;
        let significand = u64::try_from(&datum.significand).map_err(|_| FiberError::MouthRefused {
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
        let spread = u32::try_from(exponent - lowest).map_err(|_| FiberError::AlignmentSpread {
            spread: u32::MAX,
        })?;
        if spread >= 63 {
            return Err(FiberError::AlignmentSpread { spread });
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
    device_name: String,
    max_threads: u32,
    max_grid_x: u32,
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
            let device_name = CStr::from_ptr(name.as_ptr())
                .to_string_lossy()
                .into_owned();

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

            let mut loaded = [std::ptr::null_mut(); 3];
            for (slot, symbol) in loaded.iter_mut().zip([
                c"exact_readout_scores",
                c"exact_readout_scores_addressed",
                c"exact_score_octaves",
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
                device_name,
                max_threads: max_threads.max(1) as u32,
                max_grid_x: max_grid_x.max(1) as u32,
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
        entry_octaves.saturating_mul(2).saturating_add(terms).saturating_add(1)
    }

    /// **The deed.** Every exact score of one query against every declared row.
    ///
    /// `addresses` names the rows to score; `None` scores all of them. A row the caller did not name
    /// is not scored, not defaulted, and not silently included — so an aperture can report what it
    /// excluded rather than dropping it.
    pub fn score(
        &self,
        readout: &AlignedMaterial,
        query: &AlignedMaterial,
        dim: usize,
        addresses: Option<&[u32]>,
    ) -> Result<ScorePopulation, FiberError> {
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

        // The headroom check, before anything is dispatched. Refused, never truncated.
        let entry_octaves = readout.entry_octaves.max(query.entry_octaves);
        let needed = Self::needed_octaves(entry_octaves, dim);
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
                resident_chart: self.device_name.clone(),
            });
        }

        let block = self.max_threads.min(256).max(1);
        let grid = count.div_ceil(block as usize);
        if grid as u64 > u64::from(self.max_grid_x) {
            return Err(FiberError::ExtentOverflow { rows: count });
        }

        unsafe {
            checked(cuCtxSetCurrent(self.context), "cuCtxSetCurrent")?;

            let readout_bytes = std::mem::size_of_val(readout.entries.as_slice());
            let query_bytes = std::mem::size_of_val(query.entries.as_slice());
            let mut device_readout: CuDevicePtr = 0;
            let mut device_query: CuDevicePtr = 0;
            let mut device_low: CuDevicePtr = 0;
            let mut device_high: CuDevicePtr = 0;
            let mut device_octaves: CuDevicePtr = 0;
            let mut device_addresses: CuDevicePtr = 0;

            checked(cuMemAlloc_v2(&mut device_readout, readout_bytes), "cuMemAlloc(readout)")?;
            checked(cuMemAlloc_v2(&mut device_query, query_bytes), "cuMemAlloc(query)")?;
            checked(cuMemAlloc_v2(&mut device_low, count * 8), "cuMemAlloc(low)")?;
            checked(cuMemAlloc_v2(&mut device_high, count * 8), "cuMemAlloc(high)")?;
            checked(cuMemAlloc_v2(&mut device_octaves, count * 4), "cuMemAlloc(octaves)")?;

            checked(
                cuMemcpyHtoD_v2(device_readout, readout.entries.as_ptr().cast(), readout_bytes),
                "cuMemcpy(readout)",
            )?;
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
                        self.scores_addressed,
                        grid as u32, 1, 1,
                        block, 1, 1,
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
                        self.scores,
                        grid as u32, 1, 1,
                        block, 1, 1,
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
                    self.octaves,
                    grid as u32, 1, 1,
                    block, 1, 1,
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

            let _ = cuMemFree_v2(device_readout);
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
                resident_chart: self.device_name.clone(),
            })
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
        assert_eq!(scores, vec![1 * 2 + 2 * -1 + 3 * 4, -1 * 2 + 0 + 5 * 4, 7 * 2 + -7 * -1 + 0]);
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
        for (entry, expected) in aligned.entries.iter().zip([1.0f64, 2.0, 0.5, -1.5]) {
            let reproduced = *entry as f64 * 2f64.powi(aligned.exponent);
            assert_eq!(reproduced, expected, "entry {entry} exponent {}", aligned.exponent);
        }
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
            entry_octaves: entries.iter().map(|e| e.unsigned_abs().max(1).ilog2() + 1).max().unwrap_or(0),
            negatives: entries.iter().filter(|e| **e < 0).count() as u64,
            entries,
            exponent: -7,
        };
        let query_entries: Vec<i64> = (0..dim).map(|at| ((at as i64 * 97) % 255) - 127).collect();
        let query = AlignedMaterial {
            entry_octaves: query_entries.iter().map(|e| e.unsigned_abs().max(1).ilog2() + 1).max().unwrap_or(0),
            negatives: query_entries.iter().filter(|e| **e < 0).count() as u64,
            entries: query_entries,
            exponent: -3,
        };

        let carried = resident.score(&readout, &query, dim, None).expect("the deed is admissible");
        let serial = score_serially(&readout, &query, dim, None).expect("well-formed");
        assert_eq!(carried.scores, serial, "the two charts disagree");
        assert_eq!(carried.exact_multiply_accumulates, (rows * dim) as u64);

        // The octave face agrees with the exact scores it was taken beside.
        for (score, octave) in carried.scores.iter().zip(&carried.octaves) {
            let expected = if *score == 0 { 0 } else { 128 - score.unsigned_abs().leading_zeros() };
            assert_eq!(*octave, expected, "score {score}");
        }

        // And the addressed form agrees with the whole one on the rows it named.
        let named: Vec<u32> = vec![7, 0, 511, 256];
        let addressed = resident.score(&readout, &query, dim, Some(&named)).expect("admissible");
        for (slot, row) in named.iter().enumerate() {
            assert_eq!(addressed.scores[slot], carried.scores[*row as usize]);
        }
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
        assert_eq!(population.octave_census(), BTreeMap::from([(1, 1), (3, 1), (4, 3)]));
        assert_eq!(population.exact(2), Some(BigInt::from(9)));
    }
}
