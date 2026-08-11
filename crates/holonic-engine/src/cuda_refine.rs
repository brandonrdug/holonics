//! The partition refinement shell, enacted on the card.
//!
//! **GPU-first, not GPU-later.** Brandon, 2026-08-10: *"the card's integration is so fucking
//! important and you can't just keep punting it… every time we have to go from it not being
//! integrated to integrating it, you risk contamination. It's GPU first."* This module exists so
//! that the front `token_invariance` walks is enacted on the device from the beginning, with the
//! host law standing beside it as the exact reference rather than as the implementation.
//!
//! # What crosses, and why it is small
//!
//! A receiver's reading of a surface is `[kind, weight, density, conduct token]`. Two occurrences
//! agree at an offset exactly when those four words agree, so the host assigns each **distinct
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
//! count always leaves an empty slot and every probe terminates. The host sizes it as the next power
//! of two above the site count — **derived from the material, no load factor, no number chosen.**
//!
//! # Launch geometry
//!
//! Read off the device and the kernel, as `cuda_aperture` and `cuda_relation` now do:
//! `block = min(function max, device max)` taken down to a whole warp, grid refused by name past
//! the device's own `MAX_GRID_DIM_X`.

use std::collections::BTreeMap;
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
    fn cuModuleGetFunction(function: *mut CuFunction, module: CuModule, name: *const c_char) -> i32;
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
}

fn text(query: unsafe extern "C" fn(i32, *mut *const c_char) -> i32, code: i32) -> String {
    let mut out = ptr::null();
    let status = unsafe { query(code, &mut out) };
    if status == CUDA_SUCCESS && !out.is_null() {
        unsafe { CStr::from_ptr(out) }.to_string_lossy().into_owned()
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
        driver(unsafe { cuMemAlloc_v2(&mut pointer, bytes.max(1)) }, "cuMemAlloc_v2")?;
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
        driver(unsafe { cuMemsetD8_v2(self.pointer, byte, bytes) }, "cuMemsetD8_v2")
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
    claimed: CuFunction,
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

            let attribute = |selector: i32, operation: &'static str| -> Result<u32, CudaRefineError> {
                let mut value = 0i32;
                driver(cuDeviceGetAttribute(&mut value, selector, device), operation)?;
                Ok(value.max(0) as u32)
            };
            let device_block = attribute(
                DEVICE_MAX_THREADS_PER_BLOCK,
                "cuDeviceGetAttribute(MAX_THREADS_PER_BLOCK)",
            )?;
            let max_grid_x =
                attribute(DEVICE_MAX_GRID_DIM_X, "cuDeviceGetAttribute(MAX_GRID_DIM_X)")?;
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
            for (slot, symbol, operation) in [
                (&mut refine as *mut CuFunction, c"refine_shell", "cuModuleGetFunction(refine_shell)"),
                (&mut claimed as *mut CuFunction, c"refine_claimed", "cuModuleGetFunction(refine_claimed)"),
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
            for function in [refine, claimed] {
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
                horizon: 1,
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
        let mut host_class = vec![1u32; count];
        let device_class = Buffer::of(&host_class)?;
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
            let mut arguments: [*mut c_void; 12] = [
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
                host_class[at] = dense[slot];
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
                        host_class.as_ptr().cast(),
                        count * std::mem::size_of::<u32>(),
                    )
                },
                "cuMemcpyHtoD_v2",
            )?;
            if classes == count {
                // Every class is a singleton; no deeper shell can split anything. This is the
                // theorem the host law stops on, and it holds here for the same reason.
                break;
            }
        }

        Ok(DeviceSaturation {
            horizon: last_split.max(1),
            classes: previous_classes,
            shells,
            classes_at_one,
            site_class: host_class,
        })
    }
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
