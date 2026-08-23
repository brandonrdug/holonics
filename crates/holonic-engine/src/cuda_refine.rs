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
use std::ffi::{c_char, c_void, CStr};
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
    #[error("native recurrence {at} did not close inside its finite state population")]
    NativeRecurrenceDidNotClose { at: usize },
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
    #[error("the material-operation world-tube arrays do not form one exact addressed passage")]
    MaterialOperationPassageShape,
    #[error("the returned-constraint incidence, covector, and native action do not form one dynamic morphology passage")]
    DynamicMorphologyShape,
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
    returned_recurrence: CuFunction,
    dynamic_morphology: CuFunction,
    condensed_recurrence: CuFunction,
    heterogeneous_fusion: CuFunction,
    inference_ecology: CuFunction,
    material_operation_world_tube: CuFunction,
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
            let mut returned_recurrence = ptr::null_mut();
            let mut dynamic_morphology = ptr::null_mut();
            let mut condensed_recurrence = ptr::null_mut();
            let mut heterogeneous_fusion = ptr::null_mut();
            let mut inference_ecology = ptr::null_mut();
            let mut material_operation_world_tube = ptr::null_mut();
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
                    &mut returned_recurrence as *mut CuFunction,
                    c"return_and_recur_native",
                    "cuModuleGetFunction(return_and_recur_native)",
                ),
                (
                    &mut dynamic_morphology as *mut CuFunction,
                    c"cultivate_dynamic_morphology",
                    "cuModuleGetFunction(cultivate_dynamic_morphology)",
                ),
                (
                    &mut condensed_recurrence as *mut CuFunction,
                    c"conduct_condensed_recurrences",
                    "cuModuleGetFunction(conduct_condensed_recurrences)",
                ),
                (
                    &mut heterogeneous_fusion as *mut CuFunction,
                    c"conduct_heterogeneous_fusion",
                    "cuModuleGetFunction(conduct_heterogeneous_fusion)",
                ),
                (
                    &mut inference_ecology as *mut CuFunction,
                    c"conduct_inference_ecology",
                    "cuModuleGetFunction(conduct_inference_ecology)",
                ),
                (
                    &mut material_operation_world_tube as *mut CuFunction,
                    c"conduct_material_operation_world_tube",
                    "cuModuleGetFunction(conduct_material_operation_world_tube)",
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
                returned_recurrence,
                dynamic_morphology,
                condensed_recurrence,
                heterogeneous_fusion,
                inference_ecology,
                material_operation_world_tube,
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
                returned_recurrence,
                dynamic_morphology,
                condensed_recurrence,
                heterogeneous_fusion,
                inference_ecology,
                material_operation_world_tube,
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

/// Every finite predecessor/successor/ablation recurrence returned after one exterior difference.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceReturnedRecurrences {
    /// Row-major traces with stride `state_count + 1`; each length selects its exact prefix.
    pub predecessor_trace: Vec<u32>,
    pub successor_trace: Vec<u32>,
    pub ablated_trace: Vec<u32>,
    pub predecessor_lengths: Vec<u32>,
    pub successor_lengths: Vec<u32>,
    pub ablated_lengths: Vec<u32>,
    pub trace_stride: usize,
    pub committed: bool,
    pub control_predecessor: u32,
    pub control_successor: u32,
    pub launches: u64,
    pub synchronizations: u64,
    pub block_threads: u32,
    pub active_lanes: u32,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
}

/// One returned receiver covector, its exact adjoint support, committed/declined local action,
/// development and held-out passages, and targeted withdrawal returned by one card front.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceDynamicMorphology {
    pub returned_adjoint: Vec<i64>,
    pub predecessor_action: Vec<u32>,
    pub successor_action: Vec<u32>,
    pub withdrawn_action: Vec<u32>,
    pub predecessor_trace: Vec<u32>,
    pub successor_trace: Vec<u32>,
    pub withdrawn_trace: Vec<u32>,
    pub predecessor_lengths: Vec<u32>,
    pub successor_lengths: Vec<u32>,
    pub withdrawn_lengths: Vec<u32>,
    pub trace_stride: usize,
    pub committed: bool,
    pub supported_state: Option<u32>,
    pub launches: u64,
    pub synchronizations: u64,
    pub block_threads: u32,
    pub active_lanes: u32,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
}

/// The compact successor, retained predecessor route, and shared-generator withdrawal returned
/// from one card front. Visited incidence replaces pairwise trace scanning.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceCondensedRecurrences {
    pub predecessor_trace: Vec<u32>,
    pub successor_trace: Vec<u32>,
    pub withdrawn_trace: Vec<u32>,
    pub predecessor_lengths: Vec<u32>,
    pub successor_lengths: Vec<u32>,
    pub withdrawn_lengths: Vec<u32>,
    pub trace_stride: usize,
    pub launches: u64,
    pub synchronizations: u64,
    pub block_threads: u32,
    pub active_lanes: u32,
    pub visited_words: usize,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
}

/// One shared heterogeneous generator, its global withdrawal, and every single-port withdrawal
/// returned from one card front. The consequences are native addresses; complete source members
/// remain in the separately authenticated reconstruction fibres.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceHeterogeneousFusion {
    /// Family-major, port-major cells.
    pub predecessor_consequence: Vec<u32>,
    pub successor_consequence: Vec<u32>,
    pub shared_ablated_consequence: Vec<u32>,
    /// Row-major `[cell][withdrawn port]`.
    pub local_ablated_consequence: Vec<u32>,
    pub families: usize,
    pub ports: usize,
    pub launches: u64,
    pub synchronizations: u64,
    pub block_threads: u32,
    pub active_lanes: u32,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
}

/// The recurrent physical passage and all admitted heterogeneous faces returned by one resident
/// inference front. Alternative and ablated routes remain dissection testimony; only the
/// `selected_*` faces follow the explicit cultivation decision.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceInferenceEcology {
    pub predecessor_trace: Vec<u32>,
    pub successor_trace: Vec<u32>,
    pub withdrawn_trace: Vec<u32>,
    pub selected_trace: Vec<u32>,
    pub predecessor_lengths: Vec<u32>,
    pub successor_lengths: Vec<u32>,
    pub withdrawn_lengths: Vec<u32>,
    pub selected_lengths: Vec<u32>,
    pub trace_stride: usize,
    pub predecessor_consequence: Vec<u32>,
    pub successor_consequence: Vec<u32>,
    pub selected_consequence: Vec<u32>,
    pub shared_ablated_consequence: Vec<u32>,
    pub local_ablated_consequence: Vec<u32>,
    pub families: usize,
    pub ports: usize,
    pub committed: bool,
    pub launches: u64,
    pub synchronizations: u64,
    pub block_threads: u32,
    pub active_lanes: u32,
    pub visited_words: usize,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
}

/// One addressed material/operation pullback and unchanged I5 conduct returned from one card
/// front. Payload classes are receiver faces; situated face and M1 event lineage remain separate.
#[derive(Debug, PartialEq, Eq)]
pub struct DeviceMaterialOperationWorldTube {
    pub payload_classes: Vec<u32>,
    pub payload_comparisons: Vec<u32>,
    pub face_staging_events: Vec<u64>,
    pub face_terminal_events: Vec<u64>,
    pub contact_left_classes: Vec<u32>,
    pub contact_right_classes: Vec<u32>,
    pub contact_relations: Vec<u32>,
    pub recurrence_staging_events: Vec<u64>,
    pub recurrence_terminal_events: Vec<u64>,
    pub inference: DeviceInferenceEcology,
    pub launches: u64,
    pub synchronizations: u64,
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

    /// Return every finite predecessor/successor/targeted-ablation recurrence after one exterior
    /// difference, under one terminal synchronization.
    ///
    /// The card derives closure from repetition inside the complete finite state population. A
    /// positive returned occurrence commits the one addressed local delta; an empty return
    /// declines it. The host supplies neither a traversal capacity nor a semantic stop case.
    #[allow(clippy::too_many_arguments)]
    pub fn conduct_returned_recurrences_on_device(
        &mut self,
        states: usize,
        generators: usize,
        generator_table: &[u32],
        generator: u32,
        native_start: &[u32],
        returned_difference_octets: u64,
        delta_from: u32,
        delta_to: u32,
        control_from: u32,
    ) -> Result<DeviceReturnedRecurrences, CudaRefineError> {
        let expected = states
            .checked_mul(generators)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let trace_stride = states
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
        if states == 0
            || native_start.is_empty()
            || states > u32::MAX as usize
            || generators > u32::MAX as usize
            || native_start.len() > u32::MAX as usize
        {
            return Err(CudaRefineError::NativeActionTooWide);
        }
        if generator as usize >= generators {
            return Err(CudaRefineError::NativeGeneratorOutsideFamily {
                generator,
                generators,
            });
        }
        if let Some(state) = generator_table
            .iter()
            .chain(native_start)
            .copied()
            .chain([delta_from, delta_to, control_from])
            .find(|state| *state as usize >= states)
        {
            return Err(CudaRefineError::NativeStateOutsidePopulation { state, states });
        }

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let table = Buffer::of(generator_table)?;
        let starts = Buffer::of(native_start)?;
        let predecessor = Buffer::alloc(trace_entries * std::mem::size_of::<u32>())?;
        let successor = Buffer::alloc(trace_entries * std::mem::size_of::<u32>())?;
        let ablated = Buffer::alloc(trace_entries * std::mem::size_of::<u32>())?;
        let lengths_octets = native_start.len() * std::mem::size_of::<u32>();
        let predecessor_lengths_device = Buffer::alloc(lengths_octets)?;
        let successor_lengths_device = Buffer::alloc(lengths_octets)?;
        let ablated_lengths_device = Buffer::alloc(lengths_octets)?;
        let decision_device = Buffer::alloc(std::mem::size_of::<u32>())?;
        let control_device = Buffer::alloc(2 * std::mem::size_of::<u32>())?;
        let grid = self.grid_for(native_start.len() as u64)?;
        let mut table_pointer = table.pointer;
        let mut starts_pointer = starts.pointer;
        let mut predecessor_pointer = predecessor.pointer;
        let mut successor_pointer = successor.pointer;
        let mut ablated_pointer = ablated.pointer;
        let mut predecessor_lengths_pointer = predecessor_lengths_device.pointer;
        let mut successor_lengths_pointer = successor_lengths_device.pointer;
        let mut ablated_lengths_pointer = ablated_lengths_device.pointer;
        let mut decision_pointer = decision_device.pointer;
        let mut control_pointer = control_device.pointer;
        let mut cell_count = native_start.len() as u32;
        let mut state_count = states as u32;
        let mut generator_row = generator;
        let mut returned_octets = returned_difference_octets;
        let mut local_from = delta_from;
        let mut local_to = delta_to;
        let mut disjoint_from = control_from;
        let mut arguments: [*mut c_void; 17] = [
            &mut table_pointer as *mut u64 as *mut c_void,
            &mut starts_pointer as *mut u64 as *mut c_void,
            &mut predecessor_pointer as *mut u64 as *mut c_void,
            &mut successor_pointer as *mut u64 as *mut c_void,
            &mut ablated_pointer as *mut u64 as *mut c_void,
            &mut predecessor_lengths_pointer as *mut u64 as *mut c_void,
            &mut successor_lengths_pointer as *mut u64 as *mut c_void,
            &mut ablated_lengths_pointer as *mut u64 as *mut c_void,
            &mut decision_pointer as *mut u64 as *mut c_void,
            &mut control_pointer as *mut u64 as *mut c_void,
            &mut cell_count as *mut u32 as *mut c_void,
            &mut state_count as *mut u32 as *mut c_void,
            &mut generator_row as *mut u32 as *mut c_void,
            &mut returned_octets as *mut u64 as *mut c_void,
            &mut local_from as *mut u32 as *mut c_void,
            &mut local_to as *mut u32 as *mut c_void,
            &mut disjoint_from as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.returned_recurrence,
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
            "cuLaunchKernel(return_and_recur_native)",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.launches += 1;

        let mut predecessor_trace = vec![0u32; trace_entries];
        let mut successor_trace = vec![0u32; trace_entries];
        let mut ablated_trace = vec![0u32; trace_entries];
        let mut predecessor_lengths = vec![0u32; native_start.len()];
        let mut successor_lengths = vec![0u32; native_start.len()];
        let mut ablated_lengths = vec![0u32; native_start.len()];
        let mut decision = [0u32; 1];
        let mut control = [0u32; 2];
        predecessor.read(&mut predecessor_trace)?;
        successor.read(&mut successor_trace)?;
        ablated.read(&mut ablated_trace)?;
        predecessor_lengths_device.read(&mut predecessor_lengths)?;
        successor_lengths_device.read(&mut successor_lengths)?;
        ablated_lengths_device.read(&mut ablated_lengths)?;
        decision_device.read(&mut decision)?;
        control_device.read(&mut control)?;
        for (at, length) in predecessor_lengths
            .iter()
            .chain(&successor_lengths)
            .chain(&ablated_lengths)
            .copied()
            .enumerate()
        {
            if length < 2 || length as usize > trace_stride {
                return Err(CudaRefineError::NativeRecurrenceDidNotClose {
                    at: at % native_start.len(),
                });
            }
        }
        if decision[0] > 1 {
            return Err(CudaRefineError::NativeActionTooWide);
        }
        let table_octets = std::mem::size_of_val(generator_table) as u64;
        let start_octets = std::mem::size_of_val(native_start) as u64;
        let trace_octets = (trace_entries * std::mem::size_of::<u32>()) as u64;
        let length_octets = lengths_octets as u64;
        let scalar_ingress_octets =
            7 * std::mem::size_of::<u32>() as u64 + std::mem::size_of::<u64>() as u64;
        let scalar_egress_octets = 3 * std::mem::size_of::<u32>() as u64;
        Ok(DeviceReturnedRecurrences {
            predecessor_trace,
            successor_trace,
            ablated_trace,
            predecessor_lengths,
            successor_lengths,
            ablated_lengths,
            trace_stride,
            committed: decision[0] == 1,
            control_predecessor: control[0],
            control_successor: control[1],
            launches: 1,
            synchronizations: 1,
            block_threads: self.block_x,
            active_lanes: native_start.len() as u32,
            host_ingress_octets: table_octets + start_octets + scalar_ingress_octets,
            host_egress_octets: trace_octets * 3 + length_octets * 3 + scalar_egress_octets,
            resident_octets: table_octets
                + start_octets
                + trace_octets * 3
                + length_octets * 3
                + scalar_egress_octets,
        })
    }

    /// Form the exact returned receiver adjoint, decide one local commit, extend its supported
    /// finite action, and return predecessor/successor/withdrawal recurrences in one resident
    /// front. The card derives the added state from the predecessor population and closure from
    /// first recurrence; the host supplies neither a response extent nor a semantic phase choice.
    pub fn conduct_dynamic_morphology_on_device(
        &mut self,
        predecessor_action: &[u32],
        support_incidence: &[i32],
        returned_covector: &[i32],
        native_start: &[u32],
    ) -> Result<DeviceDynamicMorphology, CudaRefineError> {
        let predecessor_states = predecessor_action.len();
        let returns = returned_covector.len();
        let expected_incidence = predecessor_states
            .checked_mul(returns)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let successor_states = predecessor_states
            .checked_add(1)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let trace_stride = successor_states
            .checked_add(1)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let trace_entries = native_start
            .len()
            .checked_mul(trace_stride)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        if predecessor_states == 0
            || returns == 0
            || native_start.is_empty()
            || support_incidence.len() != expected_incidence
            || predecessor_states >= u32::MAX as usize
            || returns > u32::MAX as usize
            || native_start.len() > u32::MAX as usize
            || support_incidence
                .iter()
                .any(|entry| !matches!(*entry, 0 | 1))
            || returned_covector
                .iter()
                .any(|entry| !matches!(*entry, -1 | 0 | 1))
        {
            return Err(CudaRefineError::DynamicMorphologyShape);
        }
        if let Some(state) = predecessor_action
            .iter()
            .chain(native_start)
            .copied()
            .find(|state| *state as usize >= predecessor_states)
        {
            return Err(CudaRefineError::NativeStateOutsidePopulation {
                state,
                states: predecessor_states,
            });
        }

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let action = Buffer::of(predecessor_action)?;
        let incidence = Buffer::of(support_incidence)?;
        let covector = Buffer::of(returned_covector)?;
        let starts = Buffer::of(native_start)?;
        let adjoint_octets = predecessor_states * std::mem::size_of::<i64>();
        let adjoint = Buffer::alloc(adjoint_octets)?;
        let action_octets = successor_states * std::mem::size_of::<u32>();
        let predecessor_extended = Buffer::alloc(action_octets)?;
        let successor_action = Buffer::alloc(action_octets)?;
        let withdrawn_action = Buffer::alloc(action_octets)?;
        let trace_octets = trace_entries * std::mem::size_of::<u32>();
        let predecessor_trace_device = Buffer::alloc(trace_octets)?;
        let successor_trace_device = Buffer::alloc(trace_octets)?;
        let withdrawn_trace_device = Buffer::alloc(trace_octets)?;
        let length_octets = native_start.len() * std::mem::size_of::<u32>();
        let predecessor_lengths_device = Buffer::alloc(length_octets)?;
        let successor_lengths_device = Buffer::alloc(length_octets)?;
        let withdrawn_lengths_device = Buffer::alloc(length_octets)?;
        let decision_device = Buffer::alloc(std::mem::size_of::<u32>())?;
        let support_state_device = Buffer::alloc(std::mem::size_of::<u32>())?;

        let mut action_pointer = action.pointer;
        let mut incidence_pointer = incidence.pointer;
        let mut covector_pointer = covector.pointer;
        let mut starts_pointer = starts.pointer;
        let mut adjoint_pointer = adjoint.pointer;
        let mut predecessor_extended_pointer = predecessor_extended.pointer;
        let mut successor_action_pointer = successor_action.pointer;
        let mut withdrawn_action_pointer = withdrawn_action.pointer;
        let mut predecessor_trace_pointer = predecessor_trace_device.pointer;
        let mut successor_trace_pointer = successor_trace_device.pointer;
        let mut withdrawn_trace_pointer = withdrawn_trace_device.pointer;
        let mut predecessor_lengths_pointer = predecessor_lengths_device.pointer;
        let mut successor_lengths_pointer = successor_lengths_device.pointer;
        let mut withdrawn_lengths_pointer = withdrawn_lengths_device.pointer;
        let mut decision_pointer = decision_device.pointer;
        let mut support_state_pointer = support_state_device.pointer;
        let mut state_count = predecessor_states as u32;
        let mut return_count = returns as u32;
        let mut start_count = native_start.len() as u32;
        let mut arguments: [*mut c_void; 19] = [
            &mut action_pointer as *mut u64 as *mut c_void,
            &mut incidence_pointer as *mut u64 as *mut c_void,
            &mut covector_pointer as *mut u64 as *mut c_void,
            &mut starts_pointer as *mut u64 as *mut c_void,
            &mut adjoint_pointer as *mut u64 as *mut c_void,
            &mut predecessor_extended_pointer as *mut u64 as *mut c_void,
            &mut successor_action_pointer as *mut u64 as *mut c_void,
            &mut withdrawn_action_pointer as *mut u64 as *mut c_void,
            &mut predecessor_trace_pointer as *mut u64 as *mut c_void,
            &mut successor_trace_pointer as *mut u64 as *mut c_void,
            &mut withdrawn_trace_pointer as *mut u64 as *mut c_void,
            &mut predecessor_lengths_pointer as *mut u64 as *mut c_void,
            &mut successor_lengths_pointer as *mut u64 as *mut c_void,
            &mut withdrawn_lengths_pointer as *mut u64 as *mut c_void,
            &mut decision_pointer as *mut u64 as *mut c_void,
            &mut support_state_pointer as *mut u64 as *mut c_void,
            &mut state_count as *mut u32 as *mut c_void,
            &mut return_count as *mut u32 as *mut c_void,
            &mut start_count as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.dynamic_morphology,
                    1,
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
            "cuLaunchKernel(cultivate_dynamic_morphology)",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.launches += 1;

        let mut returned_adjoint = vec![0i64; predecessor_states];
        let mut predecessor_action_returned = vec![0u32; successor_states];
        let mut successor_action_returned = vec![0u32; successor_states];
        let mut withdrawn_action_returned = vec![0u32; successor_states];
        let mut predecessor_trace = vec![0u32; trace_entries];
        let mut successor_trace = vec![0u32; trace_entries];
        let mut withdrawn_trace = vec![0u32; trace_entries];
        let mut predecessor_lengths = vec![0u32; native_start.len()];
        let mut successor_lengths = vec![0u32; native_start.len()];
        let mut withdrawn_lengths = vec![0u32; native_start.len()];
        let mut decision = [0u32; 1];
        let mut support_state = [u32::MAX; 1];
        adjoint.read(&mut returned_adjoint)?;
        predecessor_extended.read(&mut predecessor_action_returned)?;
        successor_action.read(&mut successor_action_returned)?;
        withdrawn_action.read(&mut withdrawn_action_returned)?;
        predecessor_trace_device.read(&mut predecessor_trace)?;
        successor_trace_device.read(&mut successor_trace)?;
        withdrawn_trace_device.read(&mut withdrawn_trace)?;
        predecessor_lengths_device.read(&mut predecessor_lengths)?;
        successor_lengths_device.read(&mut successor_lengths)?;
        withdrawn_lengths_device.read(&mut withdrawn_lengths)?;
        decision_device.read(&mut decision)?;
        support_state_device.read(&mut support_state)?;
        if decision[0] > 1
            || support_state[0] != u32::MAX && support_state[0] as usize >= predecessor_states
        {
            return Err(CudaRefineError::DynamicMorphologyShape);
        }
        for (at, length) in predecessor_lengths
            .iter()
            .chain(&successor_lengths)
            .chain(&withdrawn_lengths)
            .copied()
            .enumerate()
        {
            if length < 2 || length as usize > trace_stride {
                return Err(CudaRefineError::NativeRecurrenceDidNotClose {
                    at: at % native_start.len(),
                });
            }
        }

        let ingress = std::mem::size_of_val(predecessor_action)
            + std::mem::size_of_val(support_incidence)
            + std::mem::size_of_val(returned_covector)
            + std::mem::size_of_val(native_start)
            + 3 * std::mem::size_of::<u32>();
        let egress = adjoint_octets
            + action_octets * 3
            + trace_octets * 3
            + length_octets * 3
            + 2 * std::mem::size_of::<u32>();
        Ok(DeviceDynamicMorphology {
            returned_adjoint,
            predecessor_action: predecessor_action_returned,
            successor_action: successor_action_returned,
            withdrawn_action: withdrawn_action_returned,
            predecessor_trace,
            successor_trace,
            withdrawn_trace,
            predecessor_lengths,
            successor_lengths,
            withdrawn_lengths,
            trace_stride,
            committed: decision[0] == 1,
            supported_state: (support_state[0] != u32::MAX).then_some(support_state[0]),
            launches: 1,
            synchronizations: 1,
            block_threads: self.block_x,
            active_lanes: native_start.len() as u32,
            host_ingress_octets: ingress as u64,
            host_egress_octets: egress as u64,
            resident_octets: (ingress + egress) as u64,
        })
    }

    /// Conduct the compact successor, the one retained predecessor override, and withdrawal of
    /// their shared generator for every admitted starting occurrence in one resident front.
    ///
    /// The only closure extent is the finite native population. A derived bitset records visited
    /// incidence, so recurrence detection is linear in the enacted trace rather than a quadratic
    /// scan of preceding boundaries. The host observes all routes only after one synchronization.
    pub fn conduct_condensed_recurrences_on_device(
        &mut self,
        successor_table: &[u32],
        native_start: &[u32],
        predecessor_from: u32,
        predecessor_to: u32,
    ) -> Result<DeviceCondensedRecurrences, CudaRefineError> {
        let states = successor_table.len();
        let trace_stride = states
            .checked_add(1)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let trace_entries = native_start
            .len()
            .checked_mul(trace_stride)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let visited_words = states
            .checked_add(u32::BITS as usize - 1)
            .ok_or(CudaRefineError::NativeActionTooWide)?
            / u32::BITS as usize;
        let visited_entries = native_start
            .len()
            .checked_mul(3)
            .and_then(|rows| rows.checked_mul(visited_words))
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        if states == 0
            || native_start.is_empty()
            || states > u32::MAX as usize
            || native_start.len() > u32::MAX as usize
            || visited_words > u32::MAX as usize
        {
            return Err(CudaRefineError::NativeActionTooWide);
        }
        if let Some(state) = successor_table
            .iter()
            .chain(native_start)
            .copied()
            .chain([predecessor_from, predecessor_to])
            .find(|state| *state as usize >= states)
        {
            return Err(CudaRefineError::NativeStateOutsidePopulation { state, states });
        }
        if successor_table[predecessor_from as usize] == predecessor_to {
            return Err(CudaRefineError::NativeActionTooWide);
        }

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let table = Buffer::of(successor_table)?;
        let starts = Buffer::of(native_start)?;
        let trace_octets = trace_entries * std::mem::size_of::<u32>();
        let predecessor = Buffer::alloc(trace_octets)?;
        let successor = Buffer::alloc(trace_octets)?;
        let withdrawn = Buffer::alloc(trace_octets)?;
        let lengths_octets = native_start.len() * std::mem::size_of::<u32>();
        let predecessor_lengths_device = Buffer::alloc(lengths_octets)?;
        let successor_lengths_device = Buffer::alloc(lengths_octets)?;
        let withdrawn_lengths_device = Buffer::alloc(lengths_octets)?;
        let visited_octets = visited_entries * std::mem::size_of::<u32>();
        let visited = Buffer::alloc(visited_octets)?;
        visited.fill(0, visited_octets)?;

        let grid = self.grid_for(native_start.len() as u64)?;
        let mut table_pointer = table.pointer;
        let mut starts_pointer = starts.pointer;
        let mut predecessor_pointer = predecessor.pointer;
        let mut successor_pointer = successor.pointer;
        let mut withdrawn_pointer = withdrawn.pointer;
        let mut predecessor_lengths_pointer = predecessor_lengths_device.pointer;
        let mut successor_lengths_pointer = successor_lengths_device.pointer;
        let mut withdrawn_lengths_pointer = withdrawn_lengths_device.pointer;
        let mut visited_pointer = visited.pointer;
        let mut cell_count = native_start.len() as u32;
        let mut state_count = states as u32;
        let mut seen_words = visited_words as u32;
        let mut local_from = predecessor_from;
        let mut local_to = predecessor_to;
        let mut arguments: [*mut c_void; 14] = [
            &mut table_pointer as *mut u64 as *mut c_void,
            &mut starts_pointer as *mut u64 as *mut c_void,
            &mut predecessor_pointer as *mut u64 as *mut c_void,
            &mut successor_pointer as *mut u64 as *mut c_void,
            &mut withdrawn_pointer as *mut u64 as *mut c_void,
            &mut predecessor_lengths_pointer as *mut u64 as *mut c_void,
            &mut successor_lengths_pointer as *mut u64 as *mut c_void,
            &mut withdrawn_lengths_pointer as *mut u64 as *mut c_void,
            &mut visited_pointer as *mut u64 as *mut c_void,
            &mut cell_count as *mut u32 as *mut c_void,
            &mut state_count as *mut u32 as *mut c_void,
            &mut seen_words as *mut u32 as *mut c_void,
            &mut local_from as *mut u32 as *mut c_void,
            &mut local_to as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.condensed_recurrence,
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
            "cuLaunchKernel(conduct_condensed_recurrences)",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.launches += 1;

        let mut predecessor_trace = vec![0u32; trace_entries];
        let mut successor_trace = vec![0u32; trace_entries];
        let mut withdrawn_trace = vec![0u32; trace_entries];
        let mut predecessor_lengths = vec![0u32; native_start.len()];
        let mut successor_lengths = vec![0u32; native_start.len()];
        let mut withdrawn_lengths = vec![0u32; native_start.len()];
        predecessor.read(&mut predecessor_trace)?;
        successor.read(&mut successor_trace)?;
        withdrawn.read(&mut withdrawn_trace)?;
        predecessor_lengths_device.read(&mut predecessor_lengths)?;
        successor_lengths_device.read(&mut successor_lengths)?;
        withdrawn_lengths_device.read(&mut withdrawn_lengths)?;
        for (at, length) in predecessor_lengths
            .iter()
            .chain(&successor_lengths)
            .chain(&withdrawn_lengths)
            .copied()
            .enumerate()
        {
            if length < 2 || length as usize > trace_stride {
                return Err(CudaRefineError::NativeRecurrenceDidNotClose {
                    at: at % native_start.len(),
                });
            }
        }

        let table_octets = std::mem::size_of_val(successor_table) as u64;
        let start_octets = std::mem::size_of_val(native_start) as u64;
        let trace_octets = trace_octets as u64;
        let length_octets = lengths_octets as u64;
        let visited_octets = visited_octets as u64;
        let scalar_ingress_octets = 5 * std::mem::size_of::<u32>() as u64;
        Ok(DeviceCondensedRecurrences {
            predecessor_trace,
            successor_trace,
            withdrawn_trace,
            predecessor_lengths,
            successor_lengths,
            withdrawn_lengths,
            trace_stride,
            launches: 1,
            synchronizations: 1,
            block_threads: self.block_x,
            active_lanes: native_start.len() as u32,
            visited_words,
            host_ingress_octets: table_octets + start_octets + scalar_ingress_octets,
            host_egress_octets: trace_octets * 3 + length_octets * 3,
            resident_octets: table_octets
                + start_octets
                + trace_octets * 3
                + length_octets * 3
                + visited_octets,
        })
    }

    /// Conduct one shared state action through every declared modality and receiver family.
    ///
    /// `decoder` is family-major, port-major, state-minor. The same `successor_action` is read by
    /// every lane; a second per-port action table is neither accepted nor constructed. The global
    /// and every single-port ablation are returned together after one terminal synchronization.
    pub fn conduct_heterogeneous_fusion_on_device(
        &mut self,
        successor_action: &[u32],
        decoder: &[u32],
        native_start: &[u32],
        families: usize,
        ports: usize,
    ) -> Result<DeviceHeterogeneousFusion, CudaRefineError> {
        let states = successor_action.len();
        let cells = families
            .checked_mul(ports)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let expected_decoder = cells
            .checked_mul(states)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let local_entries = cells
            .checked_mul(ports)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        if states == 0
            || families == 0
            || ports < 2
            || cells == 0
            || cells > u32::MAX as usize
            || states > u32::MAX as usize
            || ports > u32::MAX as usize
            || decoder.len() != expected_decoder
            || native_start.len() != cells
        {
            return Err(CudaRefineError::NativeActionTooWide);
        }
        if let Some(state) = successor_action
            .iter()
            .chain(native_start)
            .copied()
            .find(|state| *state as usize >= states)
        {
            return Err(CudaRefineError::NativeStateOutsidePopulation { state, states });
        }

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let action = Buffer::of(successor_action)?;
        let decoder_device = Buffer::of(decoder)?;
        let starts = Buffer::of(native_start)?;
        let cell_octets = cells * std::mem::size_of::<u32>();
        let predecessor = Buffer::alloc(cell_octets)?;
        let successor = Buffer::alloc(cell_octets)?;
        let shared_ablated = Buffer::alloc(cell_octets)?;
        let local_octets = local_entries * std::mem::size_of::<u32>();
        let local_ablated = Buffer::alloc(local_octets)?;

        let grid = self.grid_for(cells as u64)?;
        let mut action_pointer = action.pointer;
        let mut decoder_pointer = decoder_device.pointer;
        let mut starts_pointer = starts.pointer;
        let mut predecessor_pointer = predecessor.pointer;
        let mut successor_pointer = successor.pointer;
        let mut shared_ablated_pointer = shared_ablated.pointer;
        let mut local_ablated_pointer = local_ablated.pointer;
        let mut cell_count = cells as u32;
        let mut state_count = states as u32;
        let mut port_count = ports as u32;
        let mut arguments: [*mut c_void; 10] = [
            &mut action_pointer as *mut u64 as *mut c_void,
            &mut decoder_pointer as *mut u64 as *mut c_void,
            &mut starts_pointer as *mut u64 as *mut c_void,
            &mut predecessor_pointer as *mut u64 as *mut c_void,
            &mut successor_pointer as *mut u64 as *mut c_void,
            &mut shared_ablated_pointer as *mut u64 as *mut c_void,
            &mut local_ablated_pointer as *mut u64 as *mut c_void,
            &mut cell_count as *mut u32 as *mut c_void,
            &mut state_count as *mut u32 as *mut c_void,
            &mut port_count as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.heterogeneous_fusion,
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
            "cuLaunchKernel(conduct_heterogeneous_fusion)",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.launches += 1;

        let mut predecessor_consequence = vec![0u32; cells];
        let mut successor_consequence = vec![0u32; cells];
        let mut shared_ablated_consequence = vec![0u32; cells];
        let mut local_ablated_consequence = vec![0u32; local_entries];
        predecessor.read(&mut predecessor_consequence)?;
        successor.read(&mut successor_consequence)?;
        shared_ablated.read(&mut shared_ablated_consequence)?;
        local_ablated.read(&mut local_ablated_consequence)?;

        let action_octets = std::mem::size_of_val(successor_action) as u64;
        let decoder_octets = std::mem::size_of_val(decoder) as u64;
        let start_octets = std::mem::size_of_val(native_start) as u64;
        let cell_octets = cell_octets as u64;
        let local_octets = local_octets as u64;
        let scalar_ingress_octets = 3 * std::mem::size_of::<u32>() as u64;
        Ok(DeviceHeterogeneousFusion {
            predecessor_consequence,
            successor_consequence,
            shared_ablated_consequence,
            local_ablated_consequence,
            families,
            ports,
            launches: 1,
            synchronizations: 1,
            block_threads: self.block_x,
            active_lanes: cells as u32,
            host_ingress_octets: action_octets
                + decoder_octets
                + start_octets
                + scalar_ingress_octets,
            host_egress_octets: cell_octets * 3 + local_octets,
            resident_octets: action_octets
                + decoder_octets
                + start_octets
                + cell_octets * 3
                + local_octets,
        })
    }

    /// Conduct the recurrent passage and every admitted heterogeneous face in one resident front.
    /// The decision is data crossing the front, not a host-selected semantic branch between I3 and
    /// I4. Both alternative routes and all withdrawals return as dissection testimony.
    #[allow(clippy::too_many_arguments)]
    pub fn conduct_inference_ecology_on_device(
        &mut self,
        recurrent_action: &[u32],
        recurrent_start: &[u32],
        recurrent_predecessor_from: u32,
        recurrent_predecessor_to: u32,
        world_action: &[u32],
        world_decoder: &[u32],
        world_start: &[u32],
        families: usize,
        ports: usize,
        committed: bool,
    ) -> Result<DeviceInferenceEcology, CudaRefineError> {
        let recurrent_states = recurrent_action.len();
        let recurrent_cells = recurrent_start.len();
        let trace_stride = recurrent_states
            .checked_add(1)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let trace_entries = recurrent_cells
            .checked_mul(trace_stride)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let visited_words = recurrent_states
            .checked_add(u32::BITS as usize - 1)
            .ok_or(CudaRefineError::NativeActionTooWide)?
            / u32::BITS as usize;
        let visited_entries = recurrent_cells
            .checked_mul(4)
            .and_then(|rows| rows.checked_mul(visited_words))
            .ok_or(CudaRefineError::NativeActionTooWide)?;

        let world_states = world_action.len();
        let world_cells = families
            .checked_mul(ports)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let expected_decoder = world_cells
            .checked_mul(world_states)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let local_entries = world_cells
            .checked_mul(ports)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let active_lanes = recurrent_cells.max(world_cells);
        if recurrent_states == 0
            || recurrent_cells == 0
            || world_states == 0
            || world_cells == 0
            || ports < 2
            || world_decoder.len() != expected_decoder
            || world_start.len() != world_cells
            || active_lanes > u32::MAX as usize
            || recurrent_states > u32::MAX as usize
            || world_states > u32::MAX as usize
            || ports > u32::MAX as usize
            || visited_words > u32::MAX as usize
        {
            return Err(CudaRefineError::NativeActionTooWide);
        }
        if let Some(state) = recurrent_action
            .iter()
            .chain(recurrent_start)
            .copied()
            .chain([recurrent_predecessor_from, recurrent_predecessor_to])
            .find(|state| *state as usize >= recurrent_states)
        {
            return Err(CudaRefineError::NativeStateOutsidePopulation {
                state,
                states: recurrent_states,
            });
        }
        if recurrent_action[recurrent_predecessor_from as usize] == recurrent_predecessor_to {
            return Err(CudaRefineError::NativeActionTooWide);
        }
        if let Some(state) = world_action
            .iter()
            .chain(world_start)
            .copied()
            .find(|state| *state as usize >= world_states)
        {
            return Err(CudaRefineError::NativeStateOutsidePopulation {
                state,
                states: world_states,
            });
        }

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let recurrent_action_device = Buffer::of(recurrent_action)?;
        let recurrent_start_device = Buffer::of(recurrent_start)?;
        let trace_octets = trace_entries * std::mem::size_of::<u32>();
        let predecessor_trace_device = Buffer::alloc(trace_octets)?;
        let successor_trace_device = Buffer::alloc(trace_octets)?;
        let withdrawn_trace_device = Buffer::alloc(trace_octets)?;
        let selected_trace_device = Buffer::alloc(trace_octets)?;
        let length_octets = recurrent_cells * std::mem::size_of::<u32>();
        let predecessor_length_device = Buffer::alloc(length_octets)?;
        let successor_length_device = Buffer::alloc(length_octets)?;
        let withdrawn_length_device = Buffer::alloc(length_octets)?;
        let selected_length_device = Buffer::alloc(length_octets)?;
        let visited_octets = visited_entries * std::mem::size_of::<u32>();
        let visited_device = Buffer::alloc(visited_octets)?;
        visited_device.fill(0, visited_octets)?;

        let world_action_device = Buffer::of(world_action)?;
        let world_decoder_device = Buffer::of(world_decoder)?;
        let world_start_device = Buffer::of(world_start)?;
        let world_cell_octets = world_cells * std::mem::size_of::<u32>();
        let world_predecessor_device = Buffer::alloc(world_cell_octets)?;
        let world_successor_device = Buffer::alloc(world_cell_octets)?;
        let world_selected_device = Buffer::alloc(world_cell_octets)?;
        let world_shared_ablated_device = Buffer::alloc(world_cell_octets)?;
        let world_local_octets = local_entries * std::mem::size_of::<u32>();
        let world_local_ablated_device = Buffer::alloc(world_local_octets)?;

        let mut recurrent_action_pointer = recurrent_action_device.pointer;
        let mut recurrent_start_pointer = recurrent_start_device.pointer;
        let mut predecessor_trace_pointer = predecessor_trace_device.pointer;
        let mut successor_trace_pointer = successor_trace_device.pointer;
        let mut withdrawn_trace_pointer = withdrawn_trace_device.pointer;
        let mut selected_trace_pointer = selected_trace_device.pointer;
        let mut predecessor_length_pointer = predecessor_length_device.pointer;
        let mut successor_length_pointer = successor_length_device.pointer;
        let mut withdrawn_length_pointer = withdrawn_length_device.pointer;
        let mut selected_length_pointer = selected_length_device.pointer;
        let mut visited_pointer = visited_device.pointer;
        let mut recurrent_cell_count = recurrent_cells as u32;
        let mut recurrent_state_count = recurrent_states as u32;
        let mut recurrent_seen_words = visited_words as u32;
        let mut local_from = recurrent_predecessor_from;
        let mut local_to = recurrent_predecessor_to;
        let mut world_action_pointer = world_action_device.pointer;
        let mut world_decoder_pointer = world_decoder_device.pointer;
        let mut world_start_pointer = world_start_device.pointer;
        let mut world_predecessor_pointer = world_predecessor_device.pointer;
        let mut world_successor_pointer = world_successor_device.pointer;
        let mut world_selected_pointer = world_selected_device.pointer;
        let mut world_shared_ablated_pointer = world_shared_ablated_device.pointer;
        let mut world_local_ablated_pointer = world_local_ablated_device.pointer;
        let mut world_cell_count = world_cells as u32;
        let mut world_state_count = world_states as u32;
        let mut world_port_count = ports as u32;
        let mut decision = u32::from(committed);
        let mut arguments: [*mut c_void; 28] = [
            &mut recurrent_action_pointer as *mut u64 as *mut c_void,
            &mut recurrent_start_pointer as *mut u64 as *mut c_void,
            &mut predecessor_trace_pointer as *mut u64 as *mut c_void,
            &mut successor_trace_pointer as *mut u64 as *mut c_void,
            &mut withdrawn_trace_pointer as *mut u64 as *mut c_void,
            &mut selected_trace_pointer as *mut u64 as *mut c_void,
            &mut predecessor_length_pointer as *mut u64 as *mut c_void,
            &mut successor_length_pointer as *mut u64 as *mut c_void,
            &mut withdrawn_length_pointer as *mut u64 as *mut c_void,
            &mut selected_length_pointer as *mut u64 as *mut c_void,
            &mut visited_pointer as *mut u64 as *mut c_void,
            &mut recurrent_cell_count as *mut u32 as *mut c_void,
            &mut recurrent_state_count as *mut u32 as *mut c_void,
            &mut recurrent_seen_words as *mut u32 as *mut c_void,
            &mut local_from as *mut u32 as *mut c_void,
            &mut local_to as *mut u32 as *mut c_void,
            &mut world_action_pointer as *mut u64 as *mut c_void,
            &mut world_decoder_pointer as *mut u64 as *mut c_void,
            &mut world_start_pointer as *mut u64 as *mut c_void,
            &mut world_predecessor_pointer as *mut u64 as *mut c_void,
            &mut world_successor_pointer as *mut u64 as *mut c_void,
            &mut world_selected_pointer as *mut u64 as *mut c_void,
            &mut world_shared_ablated_pointer as *mut u64 as *mut c_void,
            &mut world_local_ablated_pointer as *mut u64 as *mut c_void,
            &mut world_cell_count as *mut u32 as *mut c_void,
            &mut world_state_count as *mut u32 as *mut c_void,
            &mut world_port_count as *mut u32 as *mut c_void,
            &mut decision as *mut u32 as *mut c_void,
        ];
        let grid = self.grid_for(active_lanes as u64)?;
        driver(
            unsafe {
                cuLaunchKernel(
                    self.inference_ecology,
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
            "cuLaunchKernel(conduct_inference_ecology)",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.launches += 1;

        let mut predecessor_trace = vec![0u32; trace_entries];
        let mut successor_trace = vec![0u32; trace_entries];
        let mut withdrawn_trace = vec![0u32; trace_entries];
        let mut selected_trace = vec![0u32; trace_entries];
        let mut predecessor_lengths = vec![0u32; recurrent_cells];
        let mut successor_lengths = vec![0u32; recurrent_cells];
        let mut withdrawn_lengths = vec![0u32; recurrent_cells];
        let mut selected_lengths = vec![0u32; recurrent_cells];
        predecessor_trace_device.read(&mut predecessor_trace)?;
        successor_trace_device.read(&mut successor_trace)?;
        withdrawn_trace_device.read(&mut withdrawn_trace)?;
        selected_trace_device.read(&mut selected_trace)?;
        predecessor_length_device.read(&mut predecessor_lengths)?;
        successor_length_device.read(&mut successor_lengths)?;
        withdrawn_length_device.read(&mut withdrawn_lengths)?;
        selected_length_device.read(&mut selected_lengths)?;
        for (at, length) in predecessor_lengths
            .iter()
            .chain(&successor_lengths)
            .chain(&withdrawn_lengths)
            .chain(&selected_lengths)
            .copied()
            .enumerate()
        {
            if length < 2 || length as usize > trace_stride {
                return Err(CudaRefineError::NativeRecurrenceDidNotClose {
                    at: at % recurrent_cells,
                });
            }
        }

        let mut predecessor_consequence = vec![0u32; world_cells];
        let mut successor_consequence = vec![0u32; world_cells];
        let mut selected_consequence = vec![0u32; world_cells];
        let mut shared_ablated_consequence = vec![0u32; world_cells];
        let mut local_ablated_consequence = vec![0u32; local_entries];
        world_predecessor_device.read(&mut predecessor_consequence)?;
        world_successor_device.read(&mut successor_consequence)?;
        world_selected_device.read(&mut selected_consequence)?;
        world_shared_ablated_device.read(&mut shared_ablated_consequence)?;
        world_local_ablated_device.read(&mut local_ablated_consequence)?;
        let selected_expected = if committed {
            (&successor_trace, &successor_lengths, &successor_consequence)
        } else {
            (
                &predecessor_trace,
                &predecessor_lengths,
                &predecessor_consequence,
            )
        };
        if &selected_trace != selected_expected.0
            || &selected_lengths != selected_expected.1
            || &selected_consequence != selected_expected.2
        {
            return Err(CudaRefineError::NativeActionTooWide);
        }

        let recurrent_action_octets = std::mem::size_of_val(recurrent_action) as u64;
        let recurrent_start_octets = std::mem::size_of_val(recurrent_start) as u64;
        let trace_octets = trace_octets as u64;
        let length_octets = length_octets as u64;
        let visited_octets = visited_octets as u64;
        let world_action_octets = std::mem::size_of_val(world_action) as u64;
        let world_decoder_octets = std::mem::size_of_val(world_decoder) as u64;
        let world_start_octets = std::mem::size_of_val(world_start) as u64;
        let world_cell_octets = world_cell_octets as u64;
        let world_local_octets = world_local_octets as u64;
        let scalar_ingress_octets = 9 * std::mem::size_of::<u32>() as u64;
        let host_ingress_octets = recurrent_action_octets
            + recurrent_start_octets
            + world_action_octets
            + world_decoder_octets
            + world_start_octets
            + scalar_ingress_octets;
        let host_egress_octets =
            trace_octets * 4 + length_octets * 4 + world_cell_octets * 4 + world_local_octets;
        Ok(DeviceInferenceEcology {
            predecessor_trace,
            successor_trace,
            withdrawn_trace,
            selected_trace,
            predecessor_lengths,
            successor_lengths,
            withdrawn_lengths,
            selected_lengths,
            trace_stride,
            predecessor_consequence,
            successor_consequence,
            selected_consequence,
            shared_ablated_consequence,
            local_ablated_consequence,
            families,
            ports,
            committed,
            launches: 1,
            synchronizations: 1,
            block_threads: self.block_x,
            active_lanes: active_lanes as u32,
            visited_words,
            host_ingress_octets,
            host_egress_octets,
            resident_octets: host_ingress_octets + host_egress_octets + visited_octets,
        })
    }

    /// Conduct one addressed material-to-operation passage through every unchanged I5 start.
    /// Presentation branches form a full pullback with the recurrent/world starts: no host-side
    /// semantic representative is chosen. Quotient, contact, M1 entry, recurrence, section, and
    /// heterogeneous consequence return under one kernel launch and one terminal synchronization.
    #[allow(clippy::too_many_arguments)]
    pub fn conduct_material_operation_world_tube_on_device(
        &mut self,
        face_payload_keys: &[[u64; 4]],
        face_branch: &[u32],
        branch_staging_events: &[u64],
        branch_terminal_events: &[u64],
        contact_from: &[u32],
        contact_to: &[u32],
        contact_relation: &[u32],
        recurrent_action: &[u32],
        recurrent_start: &[u32],
        recurrent_predecessor_from: u32,
        recurrent_predecessor_to: u32,
        world_action: &[u32],
        world_decoder: &[u32],
        world_start: &[u32],
        families: usize,
        ports: usize,
        committed: bool,
    ) -> Result<DeviceMaterialOperationWorldTube, CudaRefineError> {
        let face_count = face_payload_keys.len();
        let contact_count = contact_from.len();
        let branch_count = branch_staging_events.len();
        let recurrent_states = recurrent_action.len();
        let recurrent_cells_per_branch = recurrent_start.len();
        let world_states = world_action.len();
        let world_cells_per_branch = families
            .checked_mul(ports)
            .ok_or(CudaRefineError::MaterialOperationPassageShape)?;
        let recurrent_cells = branch_count
            .checked_mul(recurrent_cells_per_branch)
            .ok_or(CudaRefineError::MaterialOperationPassageShape)?;
        let world_cells = branch_count
            .checked_mul(world_cells_per_branch)
            .ok_or(CudaRefineError::MaterialOperationPassageShape)?;
        let total_families = branch_count
            .checked_mul(families)
            .ok_or(CudaRefineError::MaterialOperationPassageShape)?;
        if face_count == 0
            || contact_count == 0
            || branch_count < 2
            || recurrent_states == 0
            || recurrent_cells_per_branch == 0
            || world_states == 0
            || world_cells_per_branch == 0
            || ports < 2
            || face_branch.len() != face_count
            || branch_terminal_events.len() != branch_count
            || contact_to.len() != contact_count
            || contact_relation.len() != contact_count
            || world_start.len() != world_cells_per_branch
            || world_decoder.len()
                != world_cells_per_branch
                    .checked_mul(world_states)
                    .ok_or(CudaRefineError::MaterialOperationPassageShape)?
            || face_branch
                .iter()
                .any(|branch| *branch as usize >= branch_count)
            || contact_from
                .iter()
                .chain(contact_to)
                .any(|face| *face as usize >= face_count)
            || [
                face_count,
                contact_count,
                branch_count,
                recurrent_cells,
                recurrent_states,
                recurrent_cells_per_branch,
                world_cells,
                world_cells_per_branch,
                world_states,
                ports,
            ]
            .iter()
            .any(|extent| *extent > u32::MAX as usize)
        {
            return Err(CudaRefineError::MaterialOperationPassageShape);
        }
        if recurrent_action
            .iter()
            .chain(recurrent_start)
            .copied()
            .chain([recurrent_predecessor_from, recurrent_predecessor_to])
            .any(|state| state as usize >= recurrent_states)
            || recurrent_action[recurrent_predecessor_from as usize] == recurrent_predecessor_to
            || world_action
                .iter()
                .chain(world_start)
                .any(|state| *state as usize >= world_states)
        {
            return Err(CudaRefineError::MaterialOperationPassageShape);
        }

        let trace_stride = recurrent_states
            .checked_add(1)
            .ok_or(CudaRefineError::MaterialOperationPassageShape)?;
        let trace_entries = recurrent_cells
            .checked_mul(trace_stride)
            .ok_or(CudaRefineError::MaterialOperationPassageShape)?;
        let visited_words = recurrent_states
            .checked_add(u32::BITS as usize - 1)
            .ok_or(CudaRefineError::MaterialOperationPassageShape)?
            / u32::BITS as usize;
        let visited_entries = recurrent_cells
            .checked_mul(4)
            .and_then(|rows| rows.checked_mul(visited_words))
            .ok_or(CudaRefineError::MaterialOperationPassageShape)?;
        let local_entries = world_cells
            .checked_mul(ports)
            .ok_or(CudaRefineError::MaterialOperationPassageShape)?;
        let active_lanes = face_count
            .max(contact_count)
            .max(recurrent_cells)
            .max(world_cells);

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let face_key_device = Buffer::of(face_payload_keys)?;
        let face_branch_device = Buffer::of(face_branch)?;
        let branch_staging_device = Buffer::of(branch_staging_events)?;
        let branch_terminal_device = Buffer::of(branch_terminal_events)?;
        let contact_from_device = Buffer::of(contact_from)?;
        let contact_to_device = Buffer::of(contact_to)?;
        let contact_relation_device = Buffer::of(contact_relation)?;
        let face_u32_octets = face_count * std::mem::size_of::<u32>();
        let face_u64_octets = face_count * std::mem::size_of::<u64>();
        let contact_u32_octets = contact_count * std::mem::size_of::<u32>();
        let recurrence_u64_octets = recurrent_cells * std::mem::size_of::<u64>();
        let payload_class_device = Buffer::alloc(face_u32_octets)?;
        let payload_comparison_device = Buffer::alloc(face_u32_octets)?;
        let face_staging_device = Buffer::alloc(face_u64_octets)?;
        let face_terminal_device = Buffer::alloc(face_u64_octets)?;
        let contact_left_class_device = Buffer::alloc(contact_u32_octets)?;
        let contact_right_class_device = Buffer::alloc(contact_u32_octets)?;
        let contact_relation_out_device = Buffer::alloc(contact_u32_octets)?;
        let recurrence_staging_device = Buffer::alloc(recurrence_u64_octets)?;
        let recurrence_terminal_device = Buffer::alloc(recurrence_u64_octets)?;

        let recurrent_action_device = Buffer::of(recurrent_action)?;
        let recurrent_start_device = Buffer::of(recurrent_start)?;
        let trace_octets = trace_entries * std::mem::size_of::<u32>();
        let predecessor_trace_device = Buffer::alloc(trace_octets)?;
        let successor_trace_device = Buffer::alloc(trace_octets)?;
        let withdrawn_trace_device = Buffer::alloc(trace_octets)?;
        let selected_trace_device = Buffer::alloc(trace_octets)?;
        let length_octets = recurrent_cells * std::mem::size_of::<u32>();
        let predecessor_length_device = Buffer::alloc(length_octets)?;
        let successor_length_device = Buffer::alloc(length_octets)?;
        let withdrawn_length_device = Buffer::alloc(length_octets)?;
        let selected_length_device = Buffer::alloc(length_octets)?;
        let visited_octets = visited_entries * std::mem::size_of::<u32>();
        let visited_device = Buffer::alloc(visited_octets)?;
        visited_device.fill(0, visited_octets)?;

        let world_action_device = Buffer::of(world_action)?;
        let world_decoder_device = Buffer::of(world_decoder)?;
        let world_start_device = Buffer::of(world_start)?;
        let world_cell_octets = world_cells * std::mem::size_of::<u32>();
        let world_predecessor_device = Buffer::alloc(world_cell_octets)?;
        let world_successor_device = Buffer::alloc(world_cell_octets)?;
        let world_selected_device = Buffer::alloc(world_cell_octets)?;
        let world_shared_ablated_device = Buffer::alloc(world_cell_octets)?;
        let world_local_octets = local_entries * std::mem::size_of::<u32>();
        let world_local_ablated_device = Buffer::alloc(world_local_octets)?;

        let mut face_key_pointer = face_key_device.pointer;
        let mut face_branch_pointer = face_branch_device.pointer;
        let mut branch_staging_pointer = branch_staging_device.pointer;
        let mut branch_terminal_pointer = branch_terminal_device.pointer;
        let mut contact_from_pointer = contact_from_device.pointer;
        let mut contact_to_pointer = contact_to_device.pointer;
        let mut contact_relation_pointer = contact_relation_device.pointer;
        let mut payload_class_pointer = payload_class_device.pointer;
        let mut payload_comparison_pointer = payload_comparison_device.pointer;
        let mut face_staging_pointer = face_staging_device.pointer;
        let mut face_terminal_pointer = face_terminal_device.pointer;
        let mut contact_left_class_pointer = contact_left_class_device.pointer;
        let mut contact_right_class_pointer = contact_right_class_device.pointer;
        let mut contact_relation_out_pointer = contact_relation_out_device.pointer;
        let mut recurrence_staging_pointer = recurrence_staging_device.pointer;
        let mut recurrence_terminal_pointer = recurrence_terminal_device.pointer;
        let mut face_count_wire = face_count as u32;
        let mut contact_count_wire = contact_count as u32;
        let mut branch_count_wire = branch_count as u32;
        let mut recurrence_cells_per_branch_wire = recurrent_cells_per_branch as u32;
        let mut recurrent_action_pointer = recurrent_action_device.pointer;
        let mut recurrent_start_pointer = recurrent_start_device.pointer;
        let mut predecessor_trace_pointer = predecessor_trace_device.pointer;
        let mut successor_trace_pointer = successor_trace_device.pointer;
        let mut withdrawn_trace_pointer = withdrawn_trace_device.pointer;
        let mut selected_trace_pointer = selected_trace_device.pointer;
        let mut predecessor_length_pointer = predecessor_length_device.pointer;
        let mut successor_length_pointer = successor_length_device.pointer;
        let mut withdrawn_length_pointer = withdrawn_length_device.pointer;
        let mut selected_length_pointer = selected_length_device.pointer;
        let mut visited_pointer = visited_device.pointer;
        let mut recurrent_cell_count = recurrent_cells as u32;
        let mut recurrent_state_count = recurrent_states as u32;
        let mut recurrent_seen_words = visited_words as u32;
        let mut local_from = recurrent_predecessor_from;
        let mut local_to = recurrent_predecessor_to;
        let mut world_action_pointer = world_action_device.pointer;
        let mut world_decoder_pointer = world_decoder_device.pointer;
        let mut world_start_pointer = world_start_device.pointer;
        let mut world_predecessor_pointer = world_predecessor_device.pointer;
        let mut world_successor_pointer = world_successor_device.pointer;
        let mut world_selected_pointer = world_selected_device.pointer;
        let mut world_shared_ablated_pointer = world_shared_ablated_device.pointer;
        let mut world_local_ablated_pointer = world_local_ablated_device.pointer;
        let mut world_cell_count = world_cells as u32;
        let mut world_cells_per_branch_wire = world_cells_per_branch as u32;
        let mut world_state_count = world_states as u32;
        let mut world_port_count = ports as u32;
        let mut decision = u32::from(committed);
        let mut arguments: Vec<*mut c_void> = vec![
            &mut face_key_pointer as *mut u64 as *mut c_void,
            &mut face_branch_pointer as *mut u64 as *mut c_void,
            &mut branch_staging_pointer as *mut u64 as *mut c_void,
            &mut branch_terminal_pointer as *mut u64 as *mut c_void,
            &mut contact_from_pointer as *mut u64 as *mut c_void,
            &mut contact_to_pointer as *mut u64 as *mut c_void,
            &mut contact_relation_pointer as *mut u64 as *mut c_void,
            &mut payload_class_pointer as *mut u64 as *mut c_void,
            &mut payload_comparison_pointer as *mut u64 as *mut c_void,
            &mut face_staging_pointer as *mut u64 as *mut c_void,
            &mut face_terminal_pointer as *mut u64 as *mut c_void,
            &mut contact_left_class_pointer as *mut u64 as *mut c_void,
            &mut contact_right_class_pointer as *mut u64 as *mut c_void,
            &mut contact_relation_out_pointer as *mut u64 as *mut c_void,
            &mut recurrence_staging_pointer as *mut u64 as *mut c_void,
            &mut recurrence_terminal_pointer as *mut u64 as *mut c_void,
            &mut face_count_wire as *mut u32 as *mut c_void,
            &mut contact_count_wire as *mut u32 as *mut c_void,
            &mut branch_count_wire as *mut u32 as *mut c_void,
            &mut recurrence_cells_per_branch_wire as *mut u32 as *mut c_void,
            &mut recurrent_action_pointer as *mut u64 as *mut c_void,
            &mut recurrent_start_pointer as *mut u64 as *mut c_void,
            &mut predecessor_trace_pointer as *mut u64 as *mut c_void,
            &mut successor_trace_pointer as *mut u64 as *mut c_void,
            &mut withdrawn_trace_pointer as *mut u64 as *mut c_void,
            &mut selected_trace_pointer as *mut u64 as *mut c_void,
            &mut predecessor_length_pointer as *mut u64 as *mut c_void,
            &mut successor_length_pointer as *mut u64 as *mut c_void,
            &mut withdrawn_length_pointer as *mut u64 as *mut c_void,
            &mut selected_length_pointer as *mut u64 as *mut c_void,
            &mut visited_pointer as *mut u64 as *mut c_void,
            &mut recurrent_cell_count as *mut u32 as *mut c_void,
            &mut recurrent_state_count as *mut u32 as *mut c_void,
            &mut recurrent_seen_words as *mut u32 as *mut c_void,
            &mut local_from as *mut u32 as *mut c_void,
            &mut local_to as *mut u32 as *mut c_void,
            &mut world_action_pointer as *mut u64 as *mut c_void,
            &mut world_decoder_pointer as *mut u64 as *mut c_void,
            &mut world_start_pointer as *mut u64 as *mut c_void,
            &mut world_predecessor_pointer as *mut u64 as *mut c_void,
            &mut world_successor_pointer as *mut u64 as *mut c_void,
            &mut world_selected_pointer as *mut u64 as *mut c_void,
            &mut world_shared_ablated_pointer as *mut u64 as *mut c_void,
            &mut world_local_ablated_pointer as *mut u64 as *mut c_void,
            &mut world_cell_count as *mut u32 as *mut c_void,
            &mut world_cells_per_branch_wire as *mut u32 as *mut c_void,
            &mut world_state_count as *mut u32 as *mut c_void,
            &mut world_port_count as *mut u32 as *mut c_void,
            &mut decision as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.material_operation_world_tube,
                    self.grid_for(active_lanes as u64)?,
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
            "cuLaunchKernel(conduct_material_operation_world_tube)",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.launches += 1;

        let mut payload_classes = vec![0u32; face_count];
        let mut payload_comparisons = vec![0u32; face_count];
        let mut face_staging_events = vec![0u64; face_count];
        let mut face_terminal_events = vec![0u64; face_count];
        let mut contact_left_classes = vec![0u32; contact_count];
        let mut contact_right_classes = vec![0u32; contact_count];
        let mut contact_relations = vec![0u32; contact_count];
        let mut recurrence_staging_events = vec![0u64; recurrent_cells];
        let mut recurrence_terminal_events = vec![0u64; recurrent_cells];
        payload_class_device.read(&mut payload_classes)?;
        payload_comparison_device.read(&mut payload_comparisons)?;
        face_staging_device.read(&mut face_staging_events)?;
        face_terminal_device.read(&mut face_terminal_events)?;
        contact_left_class_device.read(&mut contact_left_classes)?;
        contact_right_class_device.read(&mut contact_right_classes)?;
        contact_relation_out_device.read(&mut contact_relations)?;
        recurrence_staging_device.read(&mut recurrence_staging_events)?;
        recurrence_terminal_device.read(&mut recurrence_terminal_events)?;

        let mut predecessor_trace = vec![0u32; trace_entries];
        let mut successor_trace = vec![0u32; trace_entries];
        let mut withdrawn_trace = vec![0u32; trace_entries];
        let mut selected_trace = vec![0u32; trace_entries];
        let mut predecessor_lengths = vec![0u32; recurrent_cells];
        let mut successor_lengths = vec![0u32; recurrent_cells];
        let mut withdrawn_lengths = vec![0u32; recurrent_cells];
        let mut selected_lengths = vec![0u32; recurrent_cells];
        predecessor_trace_device.read(&mut predecessor_trace)?;
        successor_trace_device.read(&mut successor_trace)?;
        withdrawn_trace_device.read(&mut withdrawn_trace)?;
        selected_trace_device.read(&mut selected_trace)?;
        predecessor_length_device.read(&mut predecessor_lengths)?;
        successor_length_device.read(&mut successor_lengths)?;
        withdrawn_length_device.read(&mut withdrawn_lengths)?;
        selected_length_device.read(&mut selected_lengths)?;
        if predecessor_lengths
            .iter()
            .chain(&successor_lengths)
            .chain(&withdrawn_lengths)
            .chain(&selected_lengths)
            .enumerate()
            .any(|(at, length)| {
                let _ = at;
                *length < 2 || *length as usize > trace_stride
            })
        {
            return Err(CudaRefineError::NativeRecurrenceDidNotClose { at: 0 });
        }

        let mut predecessor_consequence = vec![0u32; world_cells];
        let mut successor_consequence = vec![0u32; world_cells];
        let mut selected_consequence = vec![0u32; world_cells];
        let mut shared_ablated_consequence = vec![0u32; world_cells];
        let mut local_ablated_consequence = vec![0u32; local_entries];
        world_predecessor_device.read(&mut predecessor_consequence)?;
        world_successor_device.read(&mut successor_consequence)?;
        world_selected_device.read(&mut selected_consequence)?;
        world_shared_ablated_device.read(&mut shared_ablated_consequence)?;
        world_local_ablated_device.read(&mut local_ablated_consequence)?;
        let selected_expected = if committed {
            (&successor_trace, &successor_lengths, &successor_consequence)
        } else {
            (
                &predecessor_trace,
                &predecessor_lengths,
                &predecessor_consequence,
            )
        };
        if &selected_trace != selected_expected.0
            || &selected_lengths != selected_expected.1
            || &selected_consequence != selected_expected.2
            || contact_relations != contact_relation
        {
            return Err(CudaRefineError::MaterialOperationPassageShape);
        }
        for (face, branch) in face_branch.iter().copied().enumerate() {
            if face_staging_events[face] != branch_staging_events[branch as usize]
                || face_terminal_events[face] != branch_terminal_events[branch as usize]
            {
                return Err(CudaRefineError::MaterialOperationPassageShape);
            }
        }
        for at in 0..recurrent_cells {
            let branch = at / recurrent_cells_per_branch;
            if recurrence_staging_events[at] != branch_staging_events[branch]
                || recurrence_terminal_events[at] != branch_terminal_events[branch]
            {
                return Err(CudaRefineError::MaterialOperationPassageShape);
            }
        }

        let material_ingress_octets = std::mem::size_of_val(face_payload_keys) as u64
            + std::mem::size_of_val(face_branch) as u64
            + std::mem::size_of_val(branch_staging_events) as u64
            + std::mem::size_of_val(branch_terminal_events) as u64
            + std::mem::size_of_val(contact_from) as u64
            + std::mem::size_of_val(contact_to) as u64
            + std::mem::size_of_val(contact_relation) as u64;
        let inference_ingress_octets = std::mem::size_of_val(recurrent_action) as u64
            + std::mem::size_of_val(recurrent_start) as u64
            + std::mem::size_of_val(world_action) as u64
            + std::mem::size_of_val(world_decoder) as u64
            + std::mem::size_of_val(world_start) as u64
            + 14 * std::mem::size_of::<u32>() as u64;
        let material_egress_octets = (face_u32_octets * 2
            + face_u64_octets * 2
            + contact_u32_octets * 3
            + recurrence_u64_octets * 2) as u64;
        let inference_egress_octets =
            (trace_octets * 4 + length_octets * 4 + world_cell_octets * 4 + world_local_octets)
                as u64;
        let host_ingress_octets = material_ingress_octets + inference_ingress_octets;
        let host_egress_octets = material_egress_octets + inference_egress_octets;
        let inference = DeviceInferenceEcology {
            predecessor_trace,
            successor_trace,
            withdrawn_trace,
            selected_trace,
            predecessor_lengths,
            successor_lengths,
            withdrawn_lengths,
            selected_lengths,
            trace_stride,
            predecessor_consequence,
            successor_consequence,
            selected_consequence,
            shared_ablated_consequence,
            local_ablated_consequence,
            families: total_families,
            ports,
            committed,
            launches: 1,
            synchronizations: 1,
            block_threads: self.block_x,
            active_lanes: active_lanes as u32,
            visited_words,
            host_ingress_octets: inference_ingress_octets,
            host_egress_octets: inference_egress_octets,
            resident_octets: inference_ingress_octets
                + inference_egress_octets
                + visited_octets as u64,
        };
        Ok(DeviceMaterialOperationWorldTube {
            payload_classes,
            payload_comparisons,
            face_staging_events,
            face_terminal_events,
            contact_left_classes,
            contact_right_classes,
            contact_relations,
            recurrence_staging_events,
            recurrence_terminal_events,
            inference,
            launches: 1,
            synchronizations: 1,
            host_ingress_octets,
            host_egress_octets,
            resident_octets: host_ingress_octets + host_egress_octets + visited_octets as u64,
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

    /// The I2 return: finite closure, local commit, held-out change, disjoint control and targeted
    /// ablation all cross in one resident deed.
    #[test]
    #[ignore = "requires the RTX CUDA device"]
    fn the_card_returns_every_recurrence_after_one_local_difference() {
        let mut card = CudaRefineExecutor::new().expect("the card mounts");
        let returned = card
            .conduct_returned_recurrences_on_device(3, 1, &[1, 2, 1], 0, &[0, 1, 2], 17, 2, 2, 0)
            .expect("the returned recurrences close");
        assert!(returned.committed);
        assert_eq!(returned.trace_stride, 4);
        assert_eq!(returned.predecessor_lengths, vec![4, 3, 3]);
        assert_eq!(returned.successor_lengths, vec![4, 3, 2]);
        assert_eq!(returned.ablated_lengths, returned.predecessor_lengths);
        assert_eq!(&returned.predecessor_trace[..4], &[0, 1, 2, 1]);
        assert_eq!(&returned.successor_trace[..4], &[0, 1, 2, 2]);
        assert_eq!(returned.ablated_trace, returned.predecessor_trace);
        assert_eq!(returned.control_predecessor, 1);
        assert_eq!(returned.control_successor, 1);
        assert_eq!(returned.launches, 1);
        assert_eq!(returned.synchronizations, 1);
    }

    /// R3's returned receiver incidence: the card forms `A^T r`, commits the supported terminal
    /// relation, changes a later start, and returns exact withdrawal in one launch.
    #[test]
    #[ignore = "requires the RTX CUDA device"]
    fn the_card_returns_dynamic_morphology_from_the_receiver_adjoint() {
        let mut card = CudaRefineExecutor::new().expect("the card mounts");
        let returned = card
            .conduct_dynamic_morphology_on_device(
                &[0, 0],
                &[
                    1, 0, // proof/checker
                    1, 0, // exact owner
                    1, 0, // rendering
                    1, 0, // physical boundary
                    1, 0, // later operator
                ],
                &[1, 1, 1, 1, 1],
                &[0, 1],
            )
            .expect("the dynamic morphology closes");
        assert_eq!(returned.returned_adjoint, vec![5, 0]);
        assert!(returned.committed);
        assert_eq!(returned.supported_state, Some(0));
        assert_eq!(returned.predecessor_action, vec![0, 0, 2]);
        assert_eq!(returned.successor_action, vec![2, 0, 2]);
        assert_eq!(returned.withdrawn_action, returned.predecessor_action);
        assert_eq!(returned.predecessor_lengths, vec![2, 3]);
        assert_eq!(returned.successor_lengths, vec![3, 4]);
        assert_eq!(returned.withdrawn_lengths, returned.predecessor_lengths);
        assert_eq!(&returned.predecessor_trace[..4], &[0, 0, 0, 0]);
        assert_eq!(&returned.successor_trace[..4], &[0, 2, 2, 2]);
        assert_eq!(returned.withdrawn_trace, returned.predecessor_trace);
        assert_eq!(returned.launches, 1);
        assert_eq!(returned.synchronizations, 1);

        let declined = card
            .conduct_dynamic_morphology_on_device(
                &[0, 0],
                &[1, 0, 1, 0, 1, 0, 1, 0, 1, 0],
                &[1, 1, 1, 1, 0],
                &[0, 1],
            )
            .expect("the incomplete returned family declines");
        assert_eq!(declined.returned_adjoint, vec![4, 0]);
        assert!(!declined.committed);
        assert_eq!(declined.successor_action, declined.predecessor_action);
        assert_eq!(declined.successor_trace, declined.predecessor_trace);
    }

    /// I3's recurrent condensation: a visited-incidence front returns both physical routes and
    /// withdrawal of their shared generator without a host callback or authored trace extent.
    #[test]
    #[ignore = "requires the RTX CUDA device"]
    fn the_card_returns_the_condensed_routes_and_shared_generator_withdrawal() {
        let mut card = CudaRefineExecutor::new().expect("the card mounts");
        let returned = card
            .conduct_condensed_recurrences_on_device(&[1, 2, 2], &[0, 1], 2, 1)
            .expect("the condensed recurrent family closes");
        assert_eq!(returned.trace_stride, 4);
        assert_eq!(returned.predecessor_lengths, vec![4, 3]);
        assert_eq!(returned.successor_lengths, vec![4, 3]);
        assert_eq!(returned.withdrawn_lengths, vec![2, 2]);
        assert_eq!(&returned.predecessor_trace[..4], &[0, 1, 2, 1]);
        assert_eq!(&returned.successor_trace[..4], &[0, 1, 2, 2]);
        assert_eq!(&returned.withdrawn_trace[..2], &[0, 0]);
        assert_eq!(returned.launches, 1);
        assert_eq!(returned.synchronizations, 1);
        assert_eq!(returned.visited_words, 1);
    }

    /// I4's conservation-of-faces law: the shared generator moves every port, while withdrawing
    /// one port leaves the other on the shared successor.
    #[test]
    #[ignore = "requires the RTX CUDA device"]
    fn the_card_enacts_one_shared_generator_and_every_local_withdrawal() {
        let mut card = CudaRefineExecutor::new().expect("the card mounts");
        // Two families × two ports × two states. Each native consequence has its own address.
        let returned = card
            .conduct_heterogeneous_fusion_on_device(
                &[1, 1],
                &[0, 1, 2, 3, 4, 5, 6, 7],
                &[0, 0, 0, 0],
                2,
                2,
            )
            .expect("the heterogeneous front returns");
        assert_eq!(returned.predecessor_consequence, vec![0, 2, 4, 6]);
        assert_eq!(returned.successor_consequence, vec![1, 3, 5, 7]);
        assert_eq!(returned.shared_ablated_consequence, vec![0, 2, 4, 6]);
        assert_eq!(
            returned.local_ablated_consequence,
            vec![0, 1, 3, 2, 4, 5, 7, 6]
        );
        assert_eq!(returned.launches, 1);
        assert_eq!(returned.synchronizations, 1);
    }

    /// I5's composed front: recurrence and conserved text/vision faces are selected by one
    /// resident decision without a host semantic bridge.
    #[test]
    #[ignore = "requires the RTX CUDA device"]
    fn the_card_returns_one_committed_inference_ecology() {
        let mut card = CudaRefineExecutor::new().expect("the card mounts");
        let returned = card
            .conduct_inference_ecology_on_device(
                &[1, 2, 2],
                &[0, 1],
                2,
                1,
                &[1, 1],
                &[0, 1, 2, 3, 4, 5, 6, 7],
                &[0, 0, 0, 0],
                2,
                2,
                true,
            )
            .expect("the inference ecology closes");
        assert_eq!(returned.trace_stride, 4);
        assert_eq!(&returned.selected_trace[..4], &[0, 1, 2, 2]);
        assert_eq!(returned.selected_lengths, returned.successor_lengths);
        assert_eq!(returned.selected_consequence, vec![1, 3, 5, 7]);
        assert_eq!(returned.shared_ablated_consequence, vec![0, 2, 4, 6]);
        assert_eq!(returned.launches, 1);
        assert_eq!(returned.synchronizations, 1);
    }

    /// R1's full pullback: two material branches retain equal-payload quotient faces, exact
    /// contacts, their own M1 event lineage, and every I5 first future under one resident return.
    #[test]
    #[ignore = "requires the RTX CUDA device"]
    fn the_card_returns_the_material_operation_world_tube_without_selecting_a_branch() {
        let mut card = CudaRefineExecutor::new().expect("the card mounts");
        let returned = card
            .conduct_material_operation_world_tube_on_device(
                &[[1, 1, 1, 1], [2, 2, 2, 2], [1, 1, 1, 1], [3, 3, 3, 3]],
                &[0, 0, 1, 1],
                &[10, 20],
                &[11, 21],
                &[0, 1],
                &[2, 3],
                &[7, 8],
                &[1, 2, 2],
                &[0, 1],
                2,
                1,
                &[1, 1],
                &[0, 1, 2, 3, 4, 5, 6, 7],
                &[0, 0, 0, 0],
                2,
                2,
                true,
            )
            .expect("the material-operation world-tube closes");
        assert_eq!(returned.payload_classes, vec![1, 2, 1, 4]);
        assert_eq!(returned.payload_comparisons, vec![1, 2, 1, 4]);
        assert_eq!(returned.contact_left_classes, vec![1, 2]);
        assert_eq!(returned.contact_right_classes, vec![1, 4]);
        assert_eq!(returned.contact_relations, vec![7, 8]);
        assert_eq!(returned.face_staging_events, vec![10, 10, 20, 20]);
        assert_eq!(returned.face_terminal_events, vec![11, 11, 21, 21]);
        assert_eq!(returned.recurrence_staging_events, vec![10, 10, 20, 20]);
        assert_eq!(returned.recurrence_terminal_events, vec![11, 11, 21, 21]);
        assert_eq!(returned.inference.families, 4);
        assert_eq!(returned.inference.selected_lengths.len(), 4);
        assert_eq!(returned.inference.selected_consequence.len(), 8);
        assert_eq!(returned.launches, 1);
        assert_eq!(returned.synchronizations, 1);
    }
}
