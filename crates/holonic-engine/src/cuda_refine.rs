//! The partition refinement shell, enacted on the card.
//!
//! **GPU-first, not GPU-later.** Brandon, 2026-08-10: *"the card's integration is so fucking
//! important and you can't just keep punting it… every time we have to go from it not being
//! integrated to integrating it, you risk contamination. It's GPU first."* This module exists so
//! that the front `token_invariance` walks is enacted on the device from the beginning, with the
//! cpu law standing beside it as the exact reference rather than as the implementation.
//!
//! # What crosses, and why it is small
//!
//! A receiver's reading of a surface is `[kind, weight, density, conduct token]`. Two occurrences
//! agree at an offset exactly when those four words agree, so the cpu assigns each **distinct
//! reading** a dense identity once over the whole corpus — [`ReadingIdentities`] — and the device
//! compares identities. Equality of identities is equality of readings, exactly.
//!
//! Identity `0` is reserved before any reading is assigned one, and stands for an offset that has
//! run off the end of its whole. That is not a sentinel of convenience: a terminus is
//! family-invariant — deleting a receiver never merges *"the whole ended"* with a reading — so it
//! must be a value no reading can take.
//!
//! So a shell key is one `u64`, and the corpus crosses once as three `u32` arrays plus the stream.
//!
//! # The quotient is a hash join and the table cannot fill
//!
//! An occurrence's new class is the identity of `(current class, shell key)`, claimed by
//! `atomicCAS` in an open-addressed table. The atomic is on the **claim**, never on the reading.
//! Distinct pairs are at most occupied occurrences, so a capacity strictly above the occurrence
//! count always leaves an empty slot and every probe terminates. The cpu sizes it as the next power
//! of two above the site count — **derived from the material, no load factor, no number chosen.**
//!
//! # Launch geometry
//!
//! Read off the device and the kernel, as `cuda_aperture` and `cuda_relation` now do:
//! `block = min(function max, device max)` taken down to a whole warp, grid refused by name past
//! the device's own `MAX_GRID_DIM_X`.

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::{CStr, c_char, c_void};
use std::ptr;

use thiserror::Error;

use crate::corpus_census::{CorpusCensus, SurfaceId};
use crate::token_invariance::ConductAtlas;

const PTX: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/refine_shell.ptx"));
const CUDA_SUCCESS: i32 = 0;

/// The identity reserved for an offset past the end of a whole, mirroring `refine_shell.cu`.
pub const ABSENT: u32 = 0;

/// `CUdevice_attribute` / `CUfunction_attribute` selectors from `cuda.h` — ABI.
const DEVICE_MAX_THREADS_PER_BLOCK: i32 = 1;
const DEVICE_MAX_GRID_DIM_X: i32 = 5;
const DEVICE_WARP_SIZE: i32 = 10;
const FUNCTION_MAX_THREADS_PER_BLOCK: i32 = 0;

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
    fn cuMemsetD8_v2(destination: CuDevicePtr, value: u8, count: usize) -> i32;
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
pub enum CudaRefineError {
    #[error("the CUDA driver reports no device")]
    NoDevice,
    #[error("CUDA {operation} returned {code} ({name}): {message}")]
    Driver {
        operation: &'static str,
        code: i32,
        name: String,
        message: String,
    },
    #[error("the refinement extent {work} exceeds the device's declared grid aperture")]
    ExtentOverflow { work: u64 },
    #[error("a corpus of {occurrences} occurrences exceeds the exact 32-bit site wire")]
    CorpusTooWide { occurrences: usize },
    #[error(
        "the native action has {table_entries} table entries for {generators} generators and {states} states"
    )]
    NativeTableExtentDisagrees {
        table_entries: usize,
        generators: usize,
        states: usize,
    },
    #[error("native state {state} leaves the declared population of {states} states")]
    NativeStateOutsidePopulation { state: u32, states: usize },
    #[error("native generator {generator} leaves the declared family of {generators} generators")]
    NativeGeneratorOutsideFamily { generator: u32, generators: usize },
    #[error("the native action extent cannot cross the exact 32-bit device wire")]
    NativeActionTooWide,
    #[error(
        "the contact coordinate wire has {lower} lower words and {upper} upper words; both must be equal multiples of three"
    )]
    ContactCoordinateShape { lower: usize, upper: usize },
    #[error("contact coordinate interval {at} is reversed: lower {lower} exceeds upper {upper}")]
    ReversedContactCoordinate { at: usize, lower: i64, upper: i64 },
    #[error(
        "contact task {task} addresses vertex {vertex} outside the {vertices}-vertex population"
    )]
    ContactVertexOutsidePopulation {
        task: usize,
        vertex: u32,
        vertices: usize,
    },
    #[error(
        "contact comparison {comparison} addresses reading {reading} outside the {readings}-reading population"
    )]
    ContactReadingOutsidePopulation {
        comparison: usize,
        reading: u32,
        readings: usize,
    },
    #[error("the contact task and comparison index populations disagree")]
    ContactIndexShape,
    #[error("contact task {task} exceeds the exact unsigned 64-bit squared-distance wire")]
    ContactDistanceOverflow { task: usize },
    #[error("the contact passage extent cannot cross the exact 32-bit device wire")]
    ContactPassageTooWide,
}

fn text(query: unsafe extern "C" fn(i32, *mut *const c_char) -> i32, code: i32) -> String {
    let mut out = ptr::null();
    let status = unsafe { query(code, &mut out) };
    if status == CUDA_SUCCESS && !out.is_null() {
        unsafe { CStr::from_ptr(out) }
            .to_string_lossy()
            .into_owned()
    } else {
        "<no CUDA driver description>".to_owned()
    }
}

fn driver(code: i32, operation: &'static str) -> Result<(), CudaRefineError> {
    if code == CUDA_SUCCESS {
        Ok(())
    } else {
        Err(CudaRefineError::Driver {
            operation,
            code,
            name: text(cuGetErrorName, code),
            message: text(cuGetErrorString, code),
        })
    }
}

/// A device allocation owned for the life of one refinement.
struct Buffer {
    pointer: CuDevicePtr,
}

impl Buffer {
    fn alloc(bytes: usize) -> Result<Self, CudaRefineError> {
        let mut pointer = 0;
        driver(
            unsafe { cuMemAlloc_v2(&mut pointer, bytes.max(1)) },
            "cuMemAlloc_v2",
        )?;
        Ok(Self { pointer })
    }

    fn of<T: Copy>(values: &[T]) -> Result<Self, CudaRefineError> {
        let bytes = std::mem::size_of_val(values);
        let buffer = Self::alloc(bytes)?;
        if bytes > 0 {
            driver(
                unsafe { cuMemcpyHtoD_v2(buffer.pointer, values.as_ptr().cast(), bytes) },
                "cuMemcpyHtoD_v2",
            )?;
        }
        Ok(buffer)
    }

    fn read<T: Copy>(&self, into: &mut [T]) -> Result<(), CudaRefineError> {
        let bytes = std::mem::size_of_val(into);
        if bytes > 0 {
            driver(
                unsafe { cuMemcpyDtoH_v2(into.as_mut_ptr().cast(), self.pointer, bytes) },
                "cuMemcpyDtoH_v2",
            )?;
        }
        Ok(())
    }

    fn fill(&self, byte: u8, bytes: usize) -> Result<(), CudaRefineError> {
        driver(
            unsafe { cuMemsetD8_v2(self.pointer, byte, bytes) },
            "cuMemsetD8_v2",
        )
    }
}

impl Drop for Buffer {
    fn drop(&mut self) {
        unsafe {
            let _ = cuMemFree_v2(self.pointer);
        }
    }
}

/// **Every distinct reading in the corpus, given a dense identity.**
///
/// Identity `0` is reserved for a terminus before any reading is assigned one, so no reading can
/// collide with it. Built once per `(census, atlas)`; the device compares identities and never
/// reconstructs a reading.
pub struct ReadingIdentities {
    /// Indexed by `SurfaceId.0`.
    pub per_surface: Vec<u32>,
    /// How many distinct readings the corpus carries, excluding the terminus.
    pub distinct: usize,
}

impl ReadingIdentities {
    pub fn of(census: &CorpusCensus, atlas: &ConductAtlas) -> Self {
        let widest = census
            .wholes()
            .iter()
            .flat_map(|whole| whole.stream.iter())
            .map(|surface| surface.0 as usize)
            .max()
            .unwrap_or(0);
        let mut per_surface = vec![ABSENT; widest + 1];
        let mut seen: BTreeMap<[u64; 4], u32> = BTreeMap::new();
        for whole in census.wholes() {
            for surface in &whole.stream {
                let slot = surface.0 as usize;
                if per_surface[slot] != ABSENT {
                    continue;
                }
                let (kind, weight, density) = census.signature(*surface);
                let reading = [kind, weight, density, atlas.token(*surface)];
                let next = seen.len() as u32 + 1; // identity 0 is the terminus
                let identity = *seen.entry(reading).or_insert(next);
                per_surface[slot] = identity;
            }
        }
        let distinct = seen.len();
        Self {
            per_surface,
            distinct,
        }
    }
}

/// The whole corpus, laid out once for the device.
pub struct DeviceCorpus {
    whole_offset: Vec<u32>,
    whole_length: Vec<u32>,
    stream: Vec<u32>,
}

impl DeviceCorpus {
    pub fn of(census: &CorpusCensus) -> Result<Self, CudaRefineError> {
        let occurrences: usize = census.wholes().iter().map(|whole| whole.stream.len()).sum();
        if occurrences > u32::MAX as usize {
            return Err(CudaRefineError::CorpusTooWide { occurrences });
        }
        let mut whole_offset = Vec::with_capacity(census.wholes().len());
        let mut whole_length = Vec::with_capacity(census.wholes().len());
        let mut stream = Vec::with_capacity(occurrences);
        for whole in census.wholes() {
            whole_offset.push(stream.len() as u32);
            whole_length.push(whole.stream.len() as u32);
            stream.extend(whole.stream.iter().map(|surface| surface.0));
        }
        Ok(Self {
            whole_offset,
            whole_length,
            stream,
        })
    }
}

/// The card, mounted once, with the refinement law resident.
pub struct CudaRefineExecutor {
    context: CuContext,
    module: CuModule,
    refine: CuFunction,
    /// `refine_claimed` is RESOLVED AND NEVER LAUNCHED: `saturate` densifies the claimed slots on
    /// the cpu after reading them back, which supersedes the kernel's device-side compaction. The
    /// resolution stays because it is what proves the symbol is present in the committed module and
    /// because `refine_claimed`'s `MAX_THREADS_PER_BLOCK` is one of the three bounds on `block_x`;
    /// the handle stays in this field so a later launch needs no second resolution. Recorded rather
    /// than removed: an unlaunched entry point is a measurement of the module, not dead weight.
    #[allow(dead_code)]
    claimed: CuFunction,
    /// The LAW: the material-free quotient every organ with a front shares.
    claim: CuFunction,
    native_word: CuFunction,
    native_trace: CuFunction,
    contact_pairs: CuFunction,
    contact_compare: CuFunction,
    device_name: String,
    block_x: u32,
    max_grid_x: u32,
    warp: u32,
    launches: u64,
}

impl CudaRefineExecutor {
    pub fn new() -> Result<Self, CudaRefineError> {
        unsafe {
            driver(cuInit(0), "cuInit")?;
            let mut count = 0;
            driver(cuDeviceGetCount(&mut count), "cuDeviceGetCount")?;
            if count <= 0 {
                return Err(CudaRefineError::NoDevice);
            }
            let mut device = 0;
            driver(cuDeviceGet(&mut device, 0), "cuDeviceGet")?;
            let mut raw = [0 as c_char; 256];
            driver(
                cuDeviceGetName(raw.as_mut_ptr(), raw.len() as i32, device),
                "cuDeviceGetName",
            )?;
            let device_name = CStr::from_ptr(raw.as_ptr()).to_string_lossy().into_owned();

            let attribute =
                |selector: i32, operation: &'static str| -> Result<u32, CudaRefineError> {
                    let mut value = 0i32;
                    driver(
                        cuDeviceGetAttribute(&mut value, selector, device),
                        operation,
                    )?;
                    Ok(value.max(0) as u32)
                };
            let device_block = attribute(
                DEVICE_MAX_THREADS_PER_BLOCK,
                "cuDeviceGetAttribute(MAX_THREADS_PER_BLOCK)",
            )?;
            let max_grid_x = attribute(
                DEVICE_MAX_GRID_DIM_X,
                "cuDeviceGetAttribute(MAX_GRID_DIM_X)",
            )?;
            let warp = attribute(DEVICE_WARP_SIZE, "cuDeviceGetAttribute(WARP_SIZE)")?.max(1);

            let mut context = ptr::null_mut();
            driver(cuCtxCreate_v2(&mut context, 0, device), "cuCtxCreate_v2")?;

            let mut image = PTX.to_vec();
            if !image.ends_with(&[0]) {
                image.push(0);
            }
            let mut module = ptr::null_mut();
            if let Err(error) = driver(
                cuModuleLoadData(&mut module, image.as_ptr().cast()),
                "cuModuleLoadData",
            ) {
                let _ = cuCtxDestroy_v2(context);
                return Err(error);
            }
            let mut refine = ptr::null_mut();
            let mut claimed = ptr::null_mut();
            let mut claim = ptr::null_mut();
            let mut native_word = ptr::null_mut();
            let mut native_trace = ptr::null_mut();
            let mut contact_pairs = ptr::null_mut();
            let mut contact_compare = ptr::null_mut();
            for (slot, symbol, operation) in [
                (
                    &mut refine as *mut CuFunction,
                    c"refine_shell",
                    "cuModuleGetFunction(refine_shell)",
                ),
                (
                    &mut claimed as *mut CuFunction,
                    c"refine_claimed",
                    "cuModuleGetFunction(refine_claimed)",
                ),
                (
                    &mut claim as *mut CuFunction,
                    c"claim_identities",
                    "cuModuleGetFunction(claim_identities)",
                ),
                (
                    &mut native_word as *mut CuFunction,
                    c"conduct_native_word",
                    "cuModuleGetFunction(conduct_native_word)",
                ),
                (
                    &mut native_trace as *mut CuFunction,
                    c"conduct_native_trace",
                    "cuModuleGetFunction(conduct_native_trace)",
                ),
                (
                    &mut contact_pairs as *mut CuFunction,
                    c"classify_contact_pairs",
                    "cuModuleGetFunction(classify_contact_pairs)",
                ),
                (
                    &mut contact_compare as *mut CuFunction,
                    c"compare_contact_presentations",
                    "cuModuleGetFunction(compare_contact_presentations)",
                ),
            ] {
                if let Err(error) = driver(
                    cuModuleGetFunction(slot, module, symbol.as_ptr()),
                    operation,
                ) {
                    let _ = cuModuleUnload(module);
                    let _ = cuCtxDestroy_v2(context);
                    return Err(error);
                }
            }

            // The block must fit whichever the kernel and the device admit fewer of, down to a
            // whole warp: a partial warp issues with idle lanes.
            let mut kernel_block = device_block;
            for function in [
                refine,
                claimed,
                claim,
                native_word,
                native_trace,
                contact_pairs,
                contact_compare,
            ] {
                let mut value = 0i32;
                driver(
                    cuFuncGetAttribute(&mut value, FUNCTION_MAX_THREADS_PER_BLOCK, function),
                    "cuFuncGetAttribute(MAX_THREADS_PER_BLOCK)",
                )?;
                kernel_block = kernel_block.min(value.max(0) as u32);
            }
            let block_x = (kernel_block / warp).max(1) * warp;

            Ok(Self {
                context,
                module,
                refine,
                claimed,
                claim,
                native_word,
                native_trace,
                contact_pairs,
                contact_compare,
                device_name,
                block_x,
                max_grid_x,
                warp,
                launches: 0,
            })
        }
    }

    pub fn device_name(&self) -> &str {
        &self.device_name
    }

    pub fn block_threads(&self) -> u32 {
        self.block_x
    }

    pub fn warp_size(&self) -> u32 {
        self.warp
    }

    pub fn launches(&self) -> u64 {
        self.launches
    }

    fn grid_for(&self, work: u64) -> Result<u32, CudaRefineError> {
        let blocks = work.div_ceil(u64::from(self.block_x.max(1)));
        if blocks > u64::from(self.max_grid_x) {
            return Err(CudaRefineError::ExtentOverflow { work });
        }
        Ok(blocks as u32)
    }

    /// **Refine one surface's occurrence population to saturation, on the card.**
    ///
    /// One crossing per shell, one lane per occurrence. Returns the class of every site at every
    /// shell walked, and the shell at which the partition last split — which is the horizon.
    pub fn saturate(
        &mut self,
        corpus: &DeviceCorpus,
        identities: &ReadingIdentities,
        sites: &[(u32, u32)],
        ceiling: usize,
    ) -> Result<DeviceSaturation, CudaRefineError> {
        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let count = sites.len();
        if count == 0 {
            return Ok(DeviceSaturation {
                // No occurrence, so no shell ever split: the least final radius is 0. This was `1`,
                // the same authored floor the cpu law carried at `last_split.max(1)`.
                horizon: 0,
                classes: 0,
                shells: 0,
                classes_at_one: 0,
                site_class: Vec::new(),
            });
        }

        // The table can never fill: distinct pairs are at most the site count, so the next power of
        // two ABOVE it always leaves an empty slot. Derived; no load factor.
        let capacity = (count + 1).next_power_of_two();
        let mask = (capacity - 1) as u32;

        let whole: Vec<u32> = sites.iter().map(|(whole, _)| *whole).collect();
        let position: Vec<u32> = sites.iter().map(|(_, position)| *position).collect();

        let device_whole = Buffer::of(&whole)?;
        let device_position = Buffer::of(&position)?;
        let device_offset = Buffer::of(&corpus.whole_offset)?;
        let device_length = Buffer::of(&corpus.whole_length)?;
        let device_stream = Buffer::of(&corpus.stream)?;
        let device_reading = Buffer::of(&identities.per_surface)?;
        let table_pair = Buffer::alloc(capacity * std::mem::size_of::<u64>())?;
        let table_key = Buffer::alloc(capacity * std::mem::size_of::<u64>())?;
        // Every site opens in one class. Class identities begin at one so they can never equal the
        // empty marker, which is all ones.
        let mut cpu_class = vec![1u32; count];
        let device_class = Buffer::of(&cpu_class)?;
        let device_next = Buffer::alloc(count * std::mem::size_of::<u32>())?;

        let mut previous_classes = 1usize;
        let mut classes_at_one = 1usize;
        let mut last_split = 0usize;
        let mut shells = 0usize;
        let grid = self.grid_for(count as u64)?;

        for depth in 1..=ceiling {
            table_pair.fill(0xff, capacity * std::mem::size_of::<u64>())?;
            table_key.fill(0xff, capacity * std::mem::size_of::<u64>())?;
            shells += 1;

            let mut site_count = count as u32;
            let mut shell_depth = depth as u32;
            let mut capacity_mask = mask;
            let arguments: [*mut c_void; 12] = [
                &mut { device_whole.pointer } as *mut u64 as *mut c_void,
                &mut { device_position.pointer } as *mut u64 as *mut c_void,
                &mut { device_class.pointer } as *mut u64 as *mut c_void,
                &mut { device_offset.pointer } as *mut u64 as *mut c_void,
                &mut { device_length.pointer } as *mut u64 as *mut c_void,
                &mut { device_stream.pointer } as *mut u64 as *mut c_void,
                &mut { device_reading.pointer } as *mut u64 as *mut c_void,
                &mut { table_pair.pointer } as *mut u64 as *mut c_void,
                &mut { table_key.pointer } as *mut u64 as *mut c_void,
                &mut { device_next.pointer } as *mut u64 as *mut c_void,
                &mut site_count as *mut u32 as *mut c_void,
                &mut shell_depth as *mut u32 as *mut c_void,
            ];
            // `capacity_mask` is the thirteenth; the array above is fixed so it is appended here.
            let mut full: Vec<*mut c_void> = arguments.to_vec();
            full.push(&mut capacity_mask as *mut u32 as *mut c_void);

            driver(
                unsafe {
                    cuLaunchKernel(
                        self.refine,
                        grid,
                        1,
                        1,
                        self.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        full.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(refine_shell)",
            )?;
            driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
            self.launches += 1;

            // The claimed slots are the new classes. Read them back and renumber densely, which
            // keeps the class identity small and keeps the table's next round exact.
            let mut next = vec![0u32; count];
            device_next.read(&mut next)?;
            let mut dense: BTreeMap<u32, u32> = BTreeMap::new();
            for slot in &next {
                let assigned = dense.len() as u32 + 1;
                dense.entry(*slot).or_insert(assigned);
            }
            for (at, slot) in next.iter().enumerate() {
                cpu_class[at] = dense[slot];
            }
            let classes = dense.len();
            if depth == 1 {
                classes_at_one = classes;
            }
            if classes > previous_classes {
                last_split = depth;
                previous_classes = classes;
            }
            driver(
                unsafe {
                    cuMemcpyHtoD_v2(
                        device_class.pointer,
                        cpu_class.as_ptr().cast(),
                        count * std::mem::size_of::<u32>(),
                    )
                },
                "cuMemcpyHtoD_v2",
            )?;
            if classes == count {
                // Every class is a singleton; no deeper shell can split anything. This is the
                // theorem the cpu law stops on, and it holds here for the same reason.
                break;
            }
        }

        Ok(DeviceSaturation {
            // `0` when no shell ever split, which is the reading and not a floor. The cpu law's
            // `SaturationHorizon::horizon` carries the same convention and the two are compared
            // directly by `the_card_refines_the_front`.
            horizon: last_split,
            classes: previous_classes,
            shells,
            classes_at_one,
            site_class: cpu_class,
        })
    }
}

/// One complete native ordered-word deed returned from the card.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceNativeWord {
    pub native_end: Vec<u32>,
    pub launches: u64,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
}

/// One complete native ordered-word trace returned from the card after one terminal read.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceNativeTrace {
    /// Row-major `[starting occurrence][word boundary]`, including the entering state.
    pub native_trace: Vec<u32>,
    pub trace_stride: usize,
    pub starting_occurrences: usize,
    pub launches: u64,
    pub synchronizations: u64,
    pub block_threads: u32,
    pub active_lanes: u32,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
}

/// One exact contact population and its matched cross-presentation successor returned from the
/// card. Contact classes use the standing wire `outside=0, inside=1, open=2`; each paired class is
/// the complete ordered pair `3*left + right`, not a collapsed changed/unchanged bit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceContactPassage {
    pub contact_classes: Vec<u8>,
    pub paired_classes: Vec<u8>,
    pub launches: u64,
    pub synchronizations: u64,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
}

impl Drop for CudaRefineExecutor {
    fn drop(&mut self) {
        unsafe {
            let _ = cuCtxSetCurrent(self.context);
            let _ = cuModuleUnload(self.module);
            let _ = cuCtxDestroy_v2(self.context);
        }
    }
}

/// What the card returned for one surface.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceSaturation {
    pub horizon: usize,
    pub classes: usize,
    pub shells: usize,
    pub classes_at_one: usize,
    /// The final class of every site, in the order the sites were supplied.
    pub site_class: Vec<u32>,
}

/// Every word surface's sites, in the census's own order — the front the card refines.
pub fn front_of(census: &CorpusCensus) -> Vec<(SurfaceId, Vec<(u32, u32)>)> {
    census
        .word_surfaces()
        .into_iter()
        .map(|surface| (surface, census.sites(surface).to_vec()))
        .collect()
}

// -------------------------------------------------------------------------------------------------
// The exact quotient: the law, material-free
// -------------------------------------------------------------------------------------------------
//
// **This is the correction that matters, and it is ontological rather than tactical.** Brandon,
// 2026-08-10: *"why the fuck do you think you have a choice about 'paths'… why is this not
// ontologically integrated -> encapsulation and factored in the codebase for streamline networking
// and interconnections based in how we expect the machine to work according to the theorem."*
//
// A device path per organ is the cabinet-of-organs failure one level down. The governing record
// fixes the ontology — *"CPU/RAM and GPU/VRAM are local charts of the same caused body"* — and
// `CLAUDE.md` §4 fixes the method: **one operation carries many materials.**
//
// So there is ONE quotient. Given a class and one 32-bit key face per cell it returns the identity
// of `(class, key)`. Wider keys cross as successive exact faces: intersection by high word and then
// low word is equality of the complete 64-bit key. It knows nothing about streams, occurrences,
// windows, states or language. Every organ with a front expresses its step as `(classes, keys)` and
// shares this; a new material writes a key law and reuses everything else.

/// Which chart of the cover enacted a quotient. A realization coordinate, never a holon.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum QuotientCarrier {
    Cpu,
    Device,
}

/// One step of an exact quotient: the dense class of every cell, and how many there are.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Quotient {
    pub cell_class: Vec<u32>,
    pub classes: usize,
    pub carrier: QuotientCarrier,
}

impl Quotient {
    /// True when two quotients induce the same equivalence on cells.
    ///
    /// **Not the same numbering.** A carrier claims identities in whatever order its lanes reach
    /// them, and requiring two carriers to agree on numbering would be requiring a realization
    /// coordinate to be causal.
    pub fn same_partition_as(&self, other: &Quotient) -> bool {
        if self.cell_class.len() != other.cell_class.len() || self.classes != other.classes {
            return false;
        }
        let mut forward: BTreeMap<u32, u32> = BTreeMap::new();
        let mut backward: BTreeMap<u32, u32> = BTreeMap::new();
        for (mine, theirs) in self.cell_class.iter().zip(&other.cell_class) {
            if *forward.entry(*mine).or_insert(*theirs) != *theirs
                || *backward.entry(*theirs).or_insert(*mine) != *mine
            {
                return false;
            }
        }
        true
    }
}

/// **The exact quotient on the cpu.** The reference every carrier is required to equal.
pub fn quotient_on_cpu(classes: &[u32], keys: &[u64]) -> Quotient {
    let mut dense: BTreeMap<(u32, u64), u32> = BTreeMap::new();
    let mut cell_class = Vec::with_capacity(classes.len());
    for (class, key) in classes.iter().zip(keys) {
        let next = dense.len() as u32 + 1;
        cell_class.push(*dense.entry((*class, *key)).or_insert(next));
    }
    Quotient {
        classes: dense.len(),
        cell_class,
        carrier: QuotientCarrier::Cpu,
    }
}

impl CudaRefineExecutor {
    /// **The exact quotient on the card.** Same law, other chart.
    ///
    /// The capacity is the next power of two above the cell count, so the table can never fill:
    /// distinct pairs are at most cells. Derived from the material; no load factor.
    pub fn quotient_on_device(
        &mut self,
        classes: &[u32],
        keys: &[u64],
    ) -> Result<Quotient, CudaRefineError> {
        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let count = classes.len();
        if count == 0 || keys.len() != count {
            return Ok(Quotient {
                cell_class: Vec::new(),
                classes: 0,
                carrier: QuotientCarrier::Device,
            });
        }
        let capacity = (count + 1).next_power_of_two();
        let mut mask = (capacity - 1) as u32;
        let table_pair = Buffer::alloc(capacity * std::mem::size_of::<u64>())?;
        let mut current = classes.to_vec();
        let grid = self.grid_for(count as u64)?;
        for half in [
            keys.iter()
                .map(|key| (key >> 32) as u32)
                .collect::<Vec<_>>(),
            keys.iter().map(|key| *key as u32).collect::<Vec<_>>(),
        ] {
            table_pair.fill(0xff, capacity * std::mem::size_of::<u64>())?;
            let device_class = Buffer::of(&current)?;
            let device_key = Buffer::of(&half)?;
            let device_next = Buffer::alloc(count * std::mem::size_of::<u32>())?;
            let mut cells = count as u32;
            // CUDA receives pointers to the argument values. These locals must live through
            // `cuLaunchKernel`; taking a raw pointer to a block-expression temporary works by
            // accident in an unoptimized build and produced address `0x30` in release.
            let mut class_pointer = device_class.pointer;
            let mut key_pointer = device_key.pointer;
            let mut table_pointer = table_pair.pointer;
            let mut next_pointer = device_next.pointer;
            let mut arguments: Vec<*mut c_void> = vec![
                &mut class_pointer as *mut u64 as *mut c_void,
                &mut key_pointer as *mut u64 as *mut c_void,
                &mut table_pointer as *mut u64 as *mut c_void,
                &mut next_pointer as *mut u64 as *mut c_void,
                &mut cells as *mut u32 as *mut c_void,
                &mut mask as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.claim,
                        grid,
                        1,
                        1,
                        self.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(claim_identities)",
            )?;
            driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
            self.launches += 1;
            let mut slots = vec![0u32; count];
            device_next.read(&mut slots)?;
            let mut dense: BTreeMap<u32, u32> = BTreeMap::new();
            for (at, slot) in slots.iter().enumerate() {
                let next = dense.len() as u32 + 1;
                current[at] = *dense.entry(*slot).or_insert(next);
            }
        }
        Ok(Quotient {
            classes: current.iter().copied().collect::<BTreeSet<_>>().len(),
            cell_class: current,
            carrier: QuotientCarrier::Device,
        })
    }

    /// Carry a population through one complete ordered word on the resident card.
    ///
    /// `generator_table` is row-major `[generator][native state]`. It, the ordered word and the
    /// starting population cross once; every intermediate state remains device-local.
    pub fn conduct_native_word_on_device(
        &mut self,
        states: usize,
        generators: usize,
        generator_table: &[u32],
        word: &[u32],
        native_start: &[u32],
    ) -> Result<DeviceNativeWord, CudaRefineError> {
        let expected = states
            .checked_mul(generators)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        if generator_table.len() != expected {
            return Err(CudaRefineError::NativeTableExtentDisagrees {
                table_entries: generator_table.len(),
                generators,
                states,
            });
        }
        if states > u32::MAX as usize
            || generators > u32::MAX as usize
            || word.len() > u32::MAX as usize
            || native_start.len() > u32::MAX as usize
        {
            return Err(CudaRefineError::NativeActionTooWide);
        }
        if let Some(state) = generator_table
            .iter()
            .chain(native_start)
            .copied()
            .find(|state| *state as usize >= states)
        {
            return Err(CudaRefineError::NativeStateOutsidePopulation { state, states });
        }
        if let Some(generator) = word
            .iter()
            .copied()
            .find(|generator| *generator as usize >= generators)
        {
            return Err(CudaRefineError::NativeGeneratorOutsideFamily {
                generator,
                generators,
            });
        }

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let table = Buffer::of(generator_table)?;
        let device_word = Buffer::of(word)?;
        let start = Buffer::of(native_start)?;
        let end = Buffer::alloc(std::mem::size_of_val(native_start))?;
        let count = native_start.len();
        if count > 0 {
            let grid = self.grid_for(count as u64)?;
            let mut table_pointer = table.pointer;
            let mut word_pointer = device_word.pointer;
            let mut start_pointer = start.pointer;
            let mut end_pointer = end.pointer;
            let mut cell_count = count as u32;
            let mut state_count = states as u32;
            let mut word_length = word.len() as u32;
            let mut arguments: Vec<*mut c_void> = vec![
                &mut table_pointer as *mut u64 as *mut c_void,
                &mut word_pointer as *mut u64 as *mut c_void,
                &mut start_pointer as *mut u64 as *mut c_void,
                &mut end_pointer as *mut u64 as *mut c_void,
                &mut cell_count as *mut u32 as *mut c_void,
                &mut state_count as *mut u32 as *mut c_void,
                &mut word_length as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.native_word,
                        grid,
                        1,
                        1,
                        self.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(conduct_native_word)",
            )?;
            driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
            self.launches += 1;
        }
        let mut native_end = vec![0u32; count];
        if count > 0 {
            end.read(&mut native_end)?;
        }
        let table_octets = std::mem::size_of_val(generator_table) as u64;
        let word_octets = std::mem::size_of_val(word) as u64;
        let state_octets = std::mem::size_of_val(native_start) as u64;
        Ok(DeviceNativeWord {
            native_end,
            launches: u64::from(count > 0),
            host_ingress_octets: table_octets + word_octets + state_octets,
            host_egress_octets: state_octets,
            resident_octets: table_octets + word_octets + state_octets * 2,
        })
    }

    /// Carry every starting occurrence through one complete ordered word and retain every
    /// intermediate boundary until the one terminal card read.
    ///
    /// This is the trace face of [`Self::conduct_native_word_on_device`], not another transition
    /// law. The word extent comes from the caller's admitted causal section. No callback, scalar
    /// winner, or stop case crosses between its steps.
    pub fn conduct_native_trace_on_device(
        &mut self,
        states: usize,
        generators: usize,
        generator_table: &[u32],
        word: &[u32],
        native_start: &[u32],
    ) -> Result<DeviceNativeTrace, CudaRefineError> {
        let expected = states
            .checked_mul(generators)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let trace_stride = word
            .len()
            .checked_add(1)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let trace_entries = native_start
            .len()
            .checked_mul(trace_stride)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        if generator_table.len() != expected {
            return Err(CudaRefineError::NativeTableExtentDisagrees {
                table_entries: generator_table.len(),
                generators,
                states,
            });
        }
        if states > u32::MAX as usize
            || generators > u32::MAX as usize
            || word.len() > u32::MAX as usize
            || trace_stride > u32::MAX as usize
            || native_start.len() > u32::MAX as usize
        {
            return Err(CudaRefineError::NativeActionTooWide);
        }
        if let Some(state) = generator_table
            .iter()
            .chain(native_start)
            .copied()
            .find(|state| *state as usize >= states)
        {
            return Err(CudaRefineError::NativeStateOutsidePopulation { state, states });
        }
        if let Some(generator) = word
            .iter()
            .copied()
            .find(|generator| *generator as usize >= generators)
        {
            return Err(CudaRefineError::NativeGeneratorOutsideFamily {
                generator,
                generators,
            });
        }

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let table = Buffer::of(generator_table)?;
        let device_word = Buffer::of(word)?;
        let start = Buffer::of(native_start)?;
        let trace = Buffer::alloc(trace_entries * std::mem::size_of::<u32>())?;
        let count = native_start.len();
        if count > 0 {
            let grid = self.grid_for(count as u64)?;
            let mut table_pointer = table.pointer;
            let mut word_pointer = device_word.pointer;
            let mut start_pointer = start.pointer;
            let mut trace_pointer = trace.pointer;
            let mut cell_count = count as u32;
            let mut state_count = states as u32;
            let mut word_length = word.len() as u32;
            let mut stride = trace_stride as u32;
            let mut arguments: [*mut c_void; 8] = [
                &mut table_pointer as *mut u64 as *mut c_void,
                &mut word_pointer as *mut u64 as *mut c_void,
                &mut start_pointer as *mut u64 as *mut c_void,
                &mut trace_pointer as *mut u64 as *mut c_void,
                &mut cell_count as *mut u32 as *mut c_void,
                &mut state_count as *mut u32 as *mut c_void,
                &mut word_length as *mut u32 as *mut c_void,
                &mut stride as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.native_trace,
                        grid,
                        1,
                        1,
                        self.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(conduct_native_trace)",
            )?;
            driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
            self.launches += 1;
        }
        let mut native_trace = vec![0u32; trace_entries];
        if count > 0 {
            trace.read(&mut native_trace)?;
        }
        let table_octets = std::mem::size_of_val(generator_table) as u64;
        let word_octets = std::mem::size_of_val(word) as u64;
        let state_octets = std::mem::size_of_val(native_start) as u64;
        let trace_octets = (trace_entries * std::mem::size_of::<u32>()) as u64;
        Ok(DeviceNativeTrace {
            native_trace,
            trace_stride,
            starting_occurrences: count,
            launches: u64::from(count > 0),
            synchronizations: u64::from(count > 0),
            block_threads: self.block_x,
            active_lanes: count as u32,
            host_ingress_octets: table_octets + word_octets + state_octets,
            host_egress_octets: trace_octets,
            resident_octets: table_octets + word_octets + state_octets + trace_octets,
        })
    }

    /// Classify exact coordinate-box contacts and compare matched presentations without returning
    /// to the host between the two laws.
    ///
    /// Every coordinate is an integer numerator over one caller-declared common denominator; the
    /// aperture has already been multiplied by that denominator squared. The host verifies only
    /// that the wire arithmetic cannot overflow. The classifications and their ordered
    /// cross-presentation pairs are enacted on the card under one terminal synchronization.
    pub fn contact_passage_on_device(
        &mut self,
        lower_xyz: &[i64],
        upper_xyz: &[i64],
        task_left: &[u32],
        task_right: &[u32],
        comparison_left: &[u32],
        comparison_right: &[u32],
        aperture_squared: u64,
    ) -> Result<DeviceContactPassage, CudaRefineError> {
        if lower_xyz.len() != upper_xyz.len() || lower_xyz.len() % 3 != 0 {
            return Err(CudaRefineError::ContactCoordinateShape {
                lower: lower_xyz.len(),
                upper: upper_xyz.len(),
            });
        }
        if task_left.len() != task_right.len() || comparison_left.len() != comparison_right.len() {
            return Err(CudaRefineError::ContactIndexShape);
        }
        let vertices = lower_xyz.len() / 3;
        if task_left.len() > u32::MAX as usize
            || comparison_left.len() > u32::MAX as usize
            || vertices > u32::MAX as usize
        {
            return Err(CudaRefineError::ContactPassageTooWide);
        }
        for (at, (lower, upper)) in lower_xyz.iter().zip(upper_xyz).enumerate() {
            if lower > upper {
                return Err(CudaRefineError::ReversedContactCoordinate {
                    at,
                    lower: *lower,
                    upper: *upper,
                });
            }
        }
        for (task, (left, right)) in task_left.iter().zip(task_right).enumerate() {
            for vertex in [*left, *right] {
                if vertex as usize >= vertices {
                    return Err(CudaRefineError::ContactVertexOutsidePopulation {
                        task,
                        vertex,
                        vertices,
                    });
                }
            }
            let mut greatest_squared = 0_u128;
            for axis in 0..3 {
                let left_at = *left as usize * 3 + axis;
                let right_at = *right as usize * 3 + axis;
                let low = i128::from(lower_xyz[left_at]) - i128::from(upper_xyz[right_at]);
                let high = i128::from(upper_xyz[left_at]) - i128::from(lower_xyz[right_at]);
                if low < i128::from(i64::MIN)
                    || low > i128::from(i64::MAX)
                    || high < i128::from(i64::MIN)
                    || high > i128::from(i64::MAX)
                {
                    return Err(CudaRefineError::ContactDistanceOverflow { task });
                }
                let far = low.unsigned_abs().max(high.unsigned_abs());
                greatest_squared = greatest_squared
                    .checked_add(
                        far.checked_mul(far)
                            .ok_or(CudaRefineError::ContactDistanceOverflow { task })?,
                    )
                    .ok_or(CudaRefineError::ContactDistanceOverflow { task })?;
            }
            if greatest_squared > u128::from(u64::MAX) {
                return Err(CudaRefineError::ContactDistanceOverflow { task });
            }
        }
        for (comparison, (left, right)) in comparison_left.iter().zip(comparison_right).enumerate()
        {
            for reading in [*left, *right] {
                if reading as usize >= task_left.len() {
                    return Err(CudaRefineError::ContactReadingOutsidePopulation {
                        comparison,
                        reading,
                        readings: task_left.len(),
                    });
                }
            }
        }

        let pair_count = task_left.len();
        let comparison_count = comparison_left.len();
        if pair_count == 0 {
            return Ok(DeviceContactPassage {
                contact_classes: Vec::new(),
                paired_classes: Vec::new(),
                launches: 0,
                synchronizations: 0,
                host_ingress_octets: 0,
                host_egress_octets: 0,
                resident_octets: 0,
            });
        }

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let lower = Buffer::of(lower_xyz)?;
        let upper = Buffer::of(upper_xyz)?;
        let left = Buffer::of(task_left)?;
        let right = Buffer::of(task_right)?;
        let classes = Buffer::alloc(pair_count * std::mem::size_of::<u8>())?;
        let comparison_left_device = Buffer::of(comparison_left)?;
        let comparison_right_device = Buffer::of(comparison_right)?;
        let paired = Buffer::alloc(comparison_count * std::mem::size_of::<u8>())?;

        let mut lower_pointer = lower.pointer;
        let mut upper_pointer = upper.pointer;
        let mut left_pointer = left.pointer;
        let mut right_pointer = right.pointer;
        let mut class_pointer = classes.pointer;
        let mut pair_count_wire = pair_count as u32;
        let mut aperture_wire = aperture_squared;
        let mut classify_arguments: Vec<*mut c_void> = vec![
            &mut lower_pointer as *mut u64 as *mut c_void,
            &mut upper_pointer as *mut u64 as *mut c_void,
            &mut left_pointer as *mut u64 as *mut c_void,
            &mut right_pointer as *mut u64 as *mut c_void,
            &mut class_pointer as *mut u64 as *mut c_void,
            &mut pair_count_wire as *mut u32 as *mut c_void,
            &mut aperture_wire as *mut u64 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.contact_pairs,
                    self.grid_for(pair_count as u64)?,
                    1,
                    1,
                    self.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    classify_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(classify_contact_pairs)",
        )?;
        let mut launches = 1_u64;

        if comparison_count > 0 {
            let mut comparison_left_pointer = comparison_left_device.pointer;
            let mut comparison_right_pointer = comparison_right_device.pointer;
            let mut paired_pointer = paired.pointer;
            let mut comparison_count_wire = comparison_count as u32;
            let mut compare_arguments: Vec<*mut c_void> = vec![
                &mut class_pointer as *mut u64 as *mut c_void,
                &mut comparison_left_pointer as *mut u64 as *mut c_void,
                &mut comparison_right_pointer as *mut u64 as *mut c_void,
                &mut paired_pointer as *mut u64 as *mut c_void,
                &mut comparison_count_wire as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.contact_compare,
                        self.grid_for(comparison_count as u64)?,
                        1,
                        1,
                        self.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        compare_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(compare_contact_presentations)",
            )?;
            launches += 1;
        }
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.launches += launches;

        let mut contact_classes = vec![0_u8; pair_count];
        classes.read(&mut contact_classes)?;
        let mut paired_classes = vec![0_u8; comparison_count];
        if comparison_count > 0 {
            paired.read(&mut paired_classes)?;
        }
        let ingress = std::mem::size_of_val(lower_xyz)
            + std::mem::size_of_val(upper_xyz)
            + std::mem::size_of_val(task_left)
            + std::mem::size_of_val(task_right)
            + std::mem::size_of_val(comparison_left)
            + std::mem::size_of_val(comparison_right);
        let egress = contact_classes.len() + paired_classes.len();
        Ok(DeviceContactPassage {
            contact_classes,
            paired_classes,
            launches,
            synchronizations: 1,
            host_ingress_octets: ingress as u64,
            host_egress_octets: egress as u64,
            resident_octets: (ingress + egress) as u64,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// **The law is one law.** The cpu and the card must return the same partition for the same
    /// `(classes, keys)`, on material built to make the table collide and to make many cells share
    /// a pair — which is where a claim race shows up and where a wrong probe walks off.
    ///
    /// `#[ignore]`d because it requires the mounted card; run with `-- --ignored`.
    #[test]
    #[ignore = "requires the RTX CUDA device"]
    fn the_quotient_is_one_law_on_both_charts() {
        let mut card = CudaRefineExecutor::new().expect("the card mounts");
        // Deterministic material with heavy sharing: many cells per pair, several classes, and keys
        // chosen so distinct pairs land near each other under any probe.
        for cells in [1usize, 2, 31, 32, 33, 1024, 40_000] {
            let classes: Vec<u32> = (0..cells).map(|at| (at % 7) as u32 + 1).collect();
            let keys: Vec<u64> = (0..cells)
                .map(|at| ((at % 11) as u64) << 32 | (at % 5) as u64)
                .collect();
            let cpu = quotient_on_cpu(&classes, &keys);
            let device = card
                .quotient_on_device(&classes, &keys)
                .expect("the card quotients");
            assert_eq!(
                cpu.classes, device.classes,
                "class count at {cells} cells: cpu {} device {}",
                cpu.classes, device.classes
            );
            assert!(
                cpu.same_partition_as(&device),
                "the two charts must induce the same equivalence at {cells} cells"
            );
            assert_eq!(cpu.carrier, QuotientCarrier::Cpu);
            assert_eq!(device.carrier, QuotientCarrier::Device);
        }
    }

    /// The cpu law is exact on its own terms, without a card. A partition is an equivalence, so
    /// this checks the property rather than the numbering.
    #[test]
    fn the_cpu_quotient_separates_exactly_on_the_pair() {
        let classes = [1u32, 1, 1, 2, 2];
        let keys = [10u64, 10, 11, 10, 11];
        let quotient = quotient_on_cpu(&classes, &keys);
        assert_eq!(quotient.classes, 4, "(1,10) (1,11) (2,10) (2,11)");
        assert_eq!(quotient.cell_class[0], quotient.cell_class[1]);
        assert_ne!(quotient.cell_class[0], quotient.cell_class[2]);
        assert_ne!(quotient.cell_class[0], quotient.cell_class[3]);
        assert!(quotient.same_partition_as(&Quotient {
            // A different numbering of the same partition must compare equal.
            cell_class: vec![9, 9, 8, 7, 6],
            classes: 4,
            carrier: QuotientCarrier::Device,
        }));
    }

    /// The physical-fold carrier: exact coordinate boxes cross once, and the matched presentation
    /// pair is formed before the one terminal synchronization.
    #[test]
    #[ignore = "requires the RTX CUDA device"]
    fn the_card_returns_contact_classes_and_the_ordered_cross_presentation_pair() {
        let mut card = CudaRefineExecutor::new().expect("the card mounts");
        // Five vertices: a free pair at squared distance 1, an occluded pair at squared distance
        // 9, and one interval [1,3] crossing the radius-2 aperture.
        let lower = [
            0_i64, 0, 0, // 0 free primary
            0, 1, 0, // 1 free secondary
            0, 0, 0, // 2 occluded primary
            0, 3, 0, // 3 occluded secondary
            1, 0, 0, // 4 uncertain secondary, x in [1,3]
        ];
        let upper = [0_i64, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0];
        let returned = card
            .contact_passage_on_device(&lower, &upper, &[0, 2, 0], &[1, 3, 4], &[0], &[1], 4)
            .expect("the exact contact passage returns");
        assert_eq!(returned.contact_classes, vec![1, 0, 2]);
        assert_eq!(returned.paired_classes, vec![3]);
        assert_eq!(returned.launches, 2);
        assert_eq!(returned.synchronizations, 1);
    }
}
