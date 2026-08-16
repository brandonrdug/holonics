//! Exact CUDA classification of a receiver-local packed relation fiber.
//!
//! This executor does not learn a relation and does not decide which chart is
//! admissible. The observation law first proves that each selected received
//! difference is `abs(scale) * abs(raw_left - raw_right)` and converts every
//! exact rational front coordinate to its equivalent integer floor or ceiling.
//! CUDA then realizes the resulting componentwise order test.  The executor
//! keeps one driver context, reusable device storage, and the most recently
//! addressed exact front resident across calls.  Admission of that compiled
//! realization belongs to the calling physical law.

use std::ffi::{CStr, c_char, c_void};
use std::ptr;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

const CUDA_SUCCESS: i32 = 0;
/// **Launch geometry is derived here too — see `cuda_aperture::DerivedLaunch` for the statement of
/// why the previous `ABI` disposition on these constants was false.** The one value that remains is
/// [`GRADE_ITEMS_PER_THREAD`], and it is not a launch level: it is a **wire constant shared with the
/// kernel**, which blocks its grade pass by the same factor at
/// `kernels/exact_relation_support.cu:370` and `:445`. Cpu and device must agree or the grade
/// mapping is wrong, and nothing in the build links the two — that is worth carrying as a defect
/// rather than dissolving into a derivation it is not.
const GRADE_ITEMS_PER_THREAD: u64 = 8;

/// `CUdevice_attribute` selectors from `cuda.h` — ABI, fixed by the foreign interface.
const DEVICE_MAX_THREADS_PER_BLOCK: i32 = 1;
const DEVICE_MAX_GRID_DIM_X: i32 = 5;
const DEVICE_WARP_SIZE: i32 = 10;

const PTX: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/exact_relation_support.ptx"));

type CuDevice = i32;
type CuContext = *mut c_void;
type CuModule = *mut c_void;
type CuFunction = *mut c_void;
type CuDevicePtr = u64;
type CuStream = *mut c_void;

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
        shared_memory_bytes: u32,
        stream: CuStream,
        kernel_parameters: *mut *mut c_void,
        extra: *mut *mut c_void,
    ) -> i32;
    fn cuCtxSynchronize() -> i32;
    fn cuGetErrorName(error: i32, name: *mut *const c_char) -> i32;
    fn cuGetErrorString(error: i32, message: *mut *const c_char) -> i32;
}

fn driver_text(query: unsafe extern "C" fn(i32, *mut *const c_char) -> i32, code: i32) -> String {
    let mut text = ptr::null();
    // SAFETY: CUDA writes one driver-owned NUL-terminated string pointer.
    let status = unsafe { query(code, &mut text) };
    if status == CUDA_SUCCESS && !text.is_null() {
        // SAFETY: successful CUDA error-string queries return a live C string.
        unsafe { CStr::from_ptr(text) }
            .to_string_lossy()
            .into_owned()
    } else {
        "<no CUDA driver description>".to_owned()
    }
}

fn driver(code: i32, operation: &'static str) -> Result<(), CudaRelationError> {
    if code == CUDA_SUCCESS {
        Ok(())
    } else {
        Err(CudaRelationError::Driver {
            operation,
            code,
            name: driver_text(cuGetErrorName, code),
            message: driver_text(cuGetErrorString, code),
        })
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct PackedRelationPair {
    pub left: u32,
    pub right: u32,
}

const _: () = assert!(std::mem::size_of::<PackedRelationPair>() == 8);

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PackedRelationWindow {
    pub prefix: u64,
    pub left: u32,
    pub right_start: u32,
    pub right_count: u32,
}

const _: () = assert!(std::mem::size_of::<PackedRelationWindow>() == 24);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct CudaClassifiedRelation {
    pub pair: PackedRelationPair,
    pub state: u8,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct CudaRelationObstruction {
    pub pair: PackedRelationPair,
    pub kind: u8,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CudaSparseRelations {
    pub relations: Vec<CudaClassifiedRelation>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CudaSparseGrade {
    /// Wire order matches `ReceiverRelationGradeCounts`.
    pub counts: [u64; 8],
    pub obstructions: Vec<CudaRelationObstruction>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct PackedRelationFront {
    pub dimension: u32,
    /// Row-major componentwise upper bounds.
    pub positive_maxima: Vec<u64>,
    /// Row-major componentwise lower bounds.
    pub negative_minima: Vec<u64>,
}

impl PackedRelationFront {
    fn counts(&self) -> Result<(u32, u32), CudaRelationError> {
        let dimension =
            usize::try_from(self.dimension).map_err(|_| CudaRelationError::ExtentOverflow)?;
        if dimension == 0
            || !self.positive_maxima.len().is_multiple_of(dimension)
            || !self.negative_minima.len().is_multiple_of(dimension)
        {
            return Err(CudaRelationError::MalformedFront);
        }
        Ok((
            u32::try_from(self.positive_maxima.len() / dimension)
                .map_err(|_| CudaRelationError::ExtentOverflow)?,
            u32::try_from(self.negative_minima.len() / dimension)
                .map_err(|_| CudaRelationError::ExtentOverflow)?,
        ))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CudaRelationReceipt {
    pub schema: String,
    pub device: String,
    pub kernel_sha256: String,
    pub point_count: u64,
    pub relation_dimension: u64,
    pub classified_pairs: u64,
    pub returned_relations: u64,
    pub cpu_to_device_octets: u64,
    pub device_to_cpu_octets: u64,
    pub launches: u64,
    pub front_uploads: u64,
    pub allocation_resizes: u64,
}

#[derive(Default)]
struct ReusableDeviceAllocation {
    pointer: CuDevicePtr,
    capacity: usize,
}

impl ReusableDeviceAllocation {
    fn ensure(&mut self, bytes: usize) -> Result<u64, CudaRelationError> {
        let bytes = bytes.max(1);
        if self.capacity >= bytes {
            return Ok(0);
        }
        if self.pointer != 0 {
            // SAFETY: the active executor context owns this allocation.
            unsafe {
                driver(cuMemFree_v2(self.pointer), "cuMemFree_v2(resize)")?;
            }
            self.pointer = 0;
            self.capacity = 0;
        }
        let mut pointer = 0;
        // SAFETY: the active CUDA context owns the checked allocation.
        unsafe {
            driver(cuMemAlloc_v2(&mut pointer, bytes), "cuMemAlloc_v2")?;
        }
        self.pointer = pointer;
        self.capacity = bytes;
        Ok(1)
    }

    fn copy_from<T>(&self, values: &[T]) -> Result<u64, CudaRelationError> {
        let bytes = std::mem::size_of_val(values);
        if bytes > self.capacity {
            return Err(CudaRelationError::AllocationExtent);
        }
        if bytes != 0 {
            // SAFETY: the device allocation has at least this caller-checked
            // extent and the source slice remains live for the synchronous
            // cpu-to-device transfer.
            unsafe {
                driver(
                    cuMemcpyHtoD_v2(self.pointer, values.as_ptr().cast(), bytes),
                    "cuMemcpyHtoD_v2",
                )?;
            }
        }
        u64::try_from(bytes).map_err(|_| CudaRelationError::ExtentOverflow)
    }

    fn copy_to<T>(&self, values: &mut [T]) -> Result<u64, CudaRelationError> {
        let bytes = std::mem::size_of_val(values);
        if bytes > self.capacity {
            return Err(CudaRelationError::AllocationExtent);
        }
        if bytes != 0 {
            // SAFETY: the destination slice owns exactly `bytes` writable
            // octets and synchronization follows before any context teardown.
            unsafe {
                driver(
                    cuMemcpyDtoH_v2(values.as_mut_ptr().cast(), self.pointer, bytes),
                    "cuMemcpyDtoH_v2",
                )?;
            }
        }
        u64::try_from(bytes).map_err(|_| CudaRelationError::ExtentOverflow)
    }

    unsafe fn release(&mut self) {
        if self.pointer != 0 {
            // SAFETY: the executor makes its owning context current before
            // releasing every retained allocation.
            unsafe {
                let _ = cuMemFree_v2(self.pointer);
            }
            self.pointer = 0;
            self.capacity = 0;
        }
    }
}

pub struct CudaExactRelationExecutor {
    /// Threads per block, taken down to a whole number of warps, from the device's own answers.
    block_x: u32,
    /// The device's X grid ceiling. Past it the extent is refused by name.
    max_grid_x: u32,
    context: CuContext,
    module: CuModule,
    all_pairs_function: CuFunction,
    addressed_pairs_function: CuFunction,
    count_addressed_positive_function: CuFunction,
    emit_addressed_positive_function: CuFunction,
    count_window_positive_function: CuFunction,
    emit_window_positive_function: CuFunction,
    grade_all_pairs_function: CuFunction,
    emit_grade_obstructions_function: CuFunction,
    device_name: String,
    kernel_sha256: String,
    points: ReusableDeviceAllocation,
    positive_front: ReusableDeviceAllocation,
    negative_front: ReusableDeviceAllocation,
    pairs: ReusableDeviceAllocation,
    order: ReusableDeviceAllocation,
    windows: ReusableDeviceAllocation,
    output: ReusableDeviceAllocation,
    membership: ReusableDeviceAllocation,
    counter: ReusableDeviceAllocation,
    grade_counts: ReusableDeviceAllocation,
    sparse_pairs: ReusableDeviceAllocation,
    sparse_states: ReusableDeviceAllocation,
    resident_front: Option<PackedRelationFront>,
}

// The driver context may be made current on another cpu thread.  The
// production owner serializes all access to an executor, and every operation
// explicitly calls `cuCtxSetCurrent` before touching retained handles.
unsafe impl Send for CudaExactRelationExecutor {}

impl CudaExactRelationExecutor {
    pub fn new() -> Result<Self, CudaRelationError> {
        // SAFETY: every driver return and produced handle is checked.
        unsafe {
            driver(cuInit(0), "cuInit")?;
            let mut count = 0;
            driver(cuDeviceGetCount(&mut count), "cuDeviceGetCount")?;
            if count <= 0 {
                return Err(CudaRelationError::NoDevice);
            }
            let mut device = 0;
            driver(cuDeviceGet(&mut device, 0), "cuDeviceGet")?;
            let mut name = [0_i8; 256];
            driver(
                cuDeviceGetName(name.as_mut_ptr(), name.len() as i32, device),
                "cuDeviceGetName",
            )?;
            let device_name = CStr::from_ptr(name.as_ptr()).to_string_lossy().into_owned();
            let attribute =
                |selector: i32, operation: &'static str| -> Result<u32, CudaRelationError> {
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
            let block_x = (device_block / warp).max(1) * warp;
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
            let mut all_pairs_function = ptr::null_mut();
            if let Err(error) = driver(
                cuModuleGetFunction(
                    &mut all_pairs_function,
                    module,
                    c"exact_relation_all_pairs".as_ptr(),
                ),
                "cuModuleGetFunction(exact_relation_all_pairs)",
            ) {
                let _ = cuModuleUnload(module);
                let _ = cuCtxDestroy_v2(context);
                return Err(error);
            }
            let mut addressed_pairs_function = ptr::null_mut();
            if let Err(error) = driver(
                cuModuleGetFunction(
                    &mut addressed_pairs_function,
                    module,
                    c"exact_relation_addressed_pairs".as_ptr(),
                ),
                "cuModuleGetFunction(exact_relation_addressed_pairs)",
            ) {
                let _ = cuModuleUnload(module);
                let _ = cuCtxDestroy_v2(context);
                return Err(error);
            }
            let mut count_addressed_positive_function = ptr::null_mut();
            if let Err(error) = driver(
                cuModuleGetFunction(
                    &mut count_addressed_positive_function,
                    module,
                    c"exact_relation_count_addressed_positive".as_ptr(),
                ),
                "cuModuleGetFunction(exact_relation_count_addressed_positive)",
            ) {
                let _ = cuModuleUnload(module);
                let _ = cuCtxDestroy_v2(context);
                return Err(error);
            }
            let mut emit_addressed_positive_function = ptr::null_mut();
            if let Err(error) = driver(
                cuModuleGetFunction(
                    &mut emit_addressed_positive_function,
                    module,
                    c"exact_relation_emit_addressed_positive".as_ptr(),
                ),
                "cuModuleGetFunction(exact_relation_emit_addressed_positive)",
            ) {
                let _ = cuModuleUnload(module);
                let _ = cuCtxDestroy_v2(context);
                return Err(error);
            }
            let mut count_window_positive_function = ptr::null_mut();
            if let Err(error) = driver(
                cuModuleGetFunction(
                    &mut count_window_positive_function,
                    module,
                    c"exact_relation_count_window_positive".as_ptr(),
                ),
                "cuModuleGetFunction(exact_relation_count_window_positive)",
            ) {
                let _ = cuModuleUnload(module);
                let _ = cuCtxDestroy_v2(context);
                return Err(error);
            }
            let mut emit_window_positive_function = ptr::null_mut();
            if let Err(error) = driver(
                cuModuleGetFunction(
                    &mut emit_window_positive_function,
                    module,
                    c"exact_relation_emit_window_positive".as_ptr(),
                ),
                "cuModuleGetFunction(exact_relation_emit_window_positive)",
            ) {
                let _ = cuModuleUnload(module);
                let _ = cuCtxDestroy_v2(context);
                return Err(error);
            }
            let mut grade_all_pairs_function = ptr::null_mut();
            if let Err(error) = driver(
                cuModuleGetFunction(
                    &mut grade_all_pairs_function,
                    module,
                    c"exact_relation_grade_all_pairs".as_ptr(),
                ),
                "cuModuleGetFunction(exact_relation_grade_all_pairs)",
            ) {
                let _ = cuModuleUnload(module);
                let _ = cuCtxDestroy_v2(context);
                return Err(error);
            }
            let mut emit_grade_obstructions_function = ptr::null_mut();
            if let Err(error) = driver(
                cuModuleGetFunction(
                    &mut emit_grade_obstructions_function,
                    module,
                    c"exact_relation_emit_grade_obstructions".as_ptr(),
                ),
                "cuModuleGetFunction(exact_relation_emit_grade_obstructions)",
            ) {
                let _ = cuModuleUnload(module);
                let _ = cuCtxDestroy_v2(context);
                return Err(error);
            }
            Ok(Self {
                block_x,
                max_grid_x,
                context,
                module,
                all_pairs_function,
                addressed_pairs_function,
                count_addressed_positive_function,
                emit_addressed_positive_function,
                count_window_positive_function,
                emit_window_positive_function,
                grade_all_pairs_function,
                emit_grade_obstructions_function,
                device_name,
                kernel_sha256: format!("{:x}", Sha256::digest(PTX)),
                points: ReusableDeviceAllocation::default(),
                positive_front: ReusableDeviceAllocation::default(),
                negative_front: ReusableDeviceAllocation::default(),
                pairs: ReusableDeviceAllocation::default(),
                order: ReusableDeviceAllocation::default(),
                windows: ReusableDeviceAllocation::default(),
                output: ReusableDeviceAllocation::default(),
                membership: ReusableDeviceAllocation::default(),
                counter: ReusableDeviceAllocation::default(),
                grade_counts: ReusableDeviceAllocation::default(),
                sparse_pairs: ReusableDeviceAllocation::default(),
                sparse_states: ReusableDeviceAllocation::default(),
                resident_front: None,
            })
        }
    }

    pub fn device_name(&self) -> &str {
        &self.device_name
    }

    pub fn kernel_sha256(&self) -> &str {
        &self.kernel_sha256
    }

    pub fn classify_all_pairs(
        &mut self,
        points: &[i64],
        point_count: u32,
        front: &PackedRelationFront,
    ) -> Result<(Vec<u8>, CudaRelationReceipt), CudaRelationError> {
        let (positive_count, negative_count) = self.validate(points, point_count, front)?;
        let pair_count = choose_two(u64::from(point_count))?;
        let output_extent =
            usize::try_from(pair_count).map_err(|_| CudaRelationError::ExtentOverflow)?;
        self.classify(
            points,
            point_count,
            None,
            front,
            positive_count,
            negative_count,
            output_extent,
            pair_count,
        )
    }

    pub fn classify_addressed_pairs(
        &mut self,
        points: &[i64],
        point_count: u32,
        pairs: &[PackedRelationPair],
        front: &PackedRelationFront,
    ) -> Result<(Vec<u8>, CudaRelationReceipt), CudaRelationError> {
        let (positive_count, negative_count) = self.validate(points, point_count, front)?;
        if pairs.iter().any(|pair| {
            pair.left >= point_count || pair.right >= point_count || pair.left >= pair.right
        }) {
            return Err(CudaRelationError::MalformedPair);
        }
        let pair_count =
            u64::try_from(pairs.len()).map_err(|_| CudaRelationError::ExtentOverflow)?;
        self.classify(
            points,
            point_count,
            Some(pairs),
            front,
            positive_count,
            negative_count,
            pairs.len(),
            pair_count,
        )
    }

    pub fn classify_positive_addressed_pairs(
        &mut self,
        points: &[i64],
        point_count: u32,
        pairs: &[PackedRelationPair],
        front: &PackedRelationFront,
    ) -> Result<(CudaSparseRelations, CudaRelationReceipt), CudaRelationError> {
        let (mut positive_count, mut negative_count) = self.validate(points, point_count, front)?;
        if pairs.iter().any(|pair| {
            pair.left >= point_count || pair.right >= point_count || pair.left >= pair.right
        }) {
            return Err(CudaRelationError::MalformedPair);
        }
        let pair_count =
            u64::try_from(pairs.len()).map_err(|_| CudaRelationError::ExtentOverflow)?;
        let (mut cpu_to_device_octets, mut allocation_resizes, front_uploads) =
            self.prepare_points_and_front(points, front)?;
        let pair_resize = self.pairs.ensure(std::mem::size_of_val(pairs))?;
        let counter_resize = self.counter.ensure(std::mem::size_of::<u64>())?;
        allocation_resizes = allocation_resizes
            .checked_add(pair_resize)
            .and_then(|value| value.checked_add(counter_resize))
            .ok_or(CudaRelationError::ExtentOverflow)?;
        cpu_to_device_octets = cpu_to_device_octets
            .checked_add(self.pairs.copy_from(pairs)?)
            .ok_or(CudaRelationError::ExtentOverflow)?;
        let zero = [0_u64];
        cpu_to_device_octets = cpu_to_device_octets
            .checked_add(self.counter.copy_from(&zero)?)
            .ok_or(CudaRelationError::ExtentOverflow)?;

        let mut launches = 0_u64;
        if !pairs.is_empty() {
            let grid = u32::try_from(pair_count.div_ceil(u64::from(self.block_x)))
                .map_err(|_| CudaRelationError::ExtentOverflow)?;
            if grid > self.max_grid_x {
                return Err(CudaRelationError::ExtentOverflow);
            }
            let mut point_pointer = self.points.pointer;
            let mut pair_pointer = self.pairs.pointer;
            let mut positive_pointer = self.positive_front.pointer;
            let mut negative_pointer = self.negative_front.pointer;
            let mut counter_pointer = self.counter.pointer;
            let mut pair_count_argument =
                u32::try_from(pairs.len()).map_err(|_| CudaRelationError::ExtentOverflow)?;
            let mut dimension = front.dimension;
            let mut arguments = [
                (&mut point_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut pair_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut positive_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut negative_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut counter_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut pair_count_argument as *mut u32).cast::<c_void>(),
                (&mut dimension as *mut u32).cast::<c_void>(),
                (&mut positive_count as *mut u32).cast::<c_void>(),
                (&mut negative_count as *mut u32).cast::<c_void>(),
            ];
            // SAFETY: arguments match the compiled sparse-count signature.
            unsafe {
                driver(
                    cuLaunchKernel(
                        self.count_addressed_positive_function,
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
                    ),
                    "cuLaunchKernel(exact_relation_count_addressed_positive)",
                )?;
                driver(cuCtxSynchronize(), "cuCtxSynchronize")?;
            }
            launches = 1;
        }

        let mut positive_extent = [0_u64];
        let mut device_to_cpu_octets = self.counter.copy_to(&mut positive_extent)?;
        if positive_extent[0] > pair_count {
            return Err(CudaRelationError::MalformedSparseOutput);
        }
        let output_extent =
            usize::try_from(positive_extent[0]).map_err(|_| CudaRelationError::ExtentOverflow)?;
        if output_extent != 0 {
            let pair_resize = self.sparse_pairs.ensure(
                output_extent
                    .checked_mul(std::mem::size_of::<PackedRelationPair>())
                    .ok_or(CudaRelationError::ExtentOverflow)?,
            )?;
            let state_resize = self.sparse_states.ensure(output_extent)?;
            allocation_resizes = allocation_resizes
                .checked_add(pair_resize)
                .and_then(|value| value.checked_add(state_resize))
                .ok_or(CudaRelationError::ExtentOverflow)?;
            cpu_to_device_octets = cpu_to_device_octets
                .checked_add(self.counter.copy_from(&zero)?)
                .ok_or(CudaRelationError::ExtentOverflow)?;

            let grid = u32::try_from(pair_count.div_ceil(u64::from(self.block_x)))
                .map_err(|_| CudaRelationError::ExtentOverflow)?;
            if grid > self.max_grid_x {
                return Err(CudaRelationError::ExtentOverflow);
            }
            let mut point_pointer = self.points.pointer;
            let mut pair_pointer = self.pairs.pointer;
            let mut positive_pointer = self.positive_front.pointer;
            let mut negative_pointer = self.negative_front.pointer;
            let mut output_pair_pointer = self.sparse_pairs.pointer;
            let mut output_state_pointer = self.sparse_states.pointer;
            let mut counter_pointer = self.counter.pointer;
            let mut pair_count_argument =
                u32::try_from(pairs.len()).map_err(|_| CudaRelationError::ExtentOverflow)?;
            let mut dimension = front.dimension;
            let mut arguments = [
                (&mut point_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut pair_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut positive_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut negative_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut output_pair_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut output_state_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut counter_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut pair_count_argument as *mut u32).cast::<c_void>(),
                (&mut dimension as *mut u32).cast::<c_void>(),
                (&mut positive_count as *mut u32).cast::<c_void>(),
                (&mut negative_count as *mut u32).cast::<c_void>(),
            ];
            // SAFETY: arguments match the compiled sparse-emission signature.
            unsafe {
                driver(
                    cuLaunchKernel(
                        self.emit_addressed_positive_function,
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
                    ),
                    "cuLaunchKernel(exact_relation_emit_addressed_positive)",
                )?;
                driver(cuCtxSynchronize(), "cuCtxSynchronize")?;
            }
            launches = launches
                .checked_add(1)
                .ok_or(CudaRelationError::ExtentOverflow)?;
        }

        let mut emitted_extent = [0_u64];
        device_to_cpu_octets = device_to_cpu_octets
            .checked_add(self.counter.copy_to(&mut emitted_extent)?)
            .ok_or(CudaRelationError::ExtentOverflow)?;
        if emitted_extent != positive_extent {
            return Err(CudaRelationError::MalformedSparseOutput);
        }
        let mut output_pairs = vec![PackedRelationPair { left: 0, right: 0 }; output_extent];
        let mut output_states = vec![0_u8; output_extent];
        let pair_octets = self.sparse_pairs.copy_to(&mut output_pairs)?;
        let state_octets = self.sparse_states.copy_to(&mut output_states)?;
        device_to_cpu_octets = device_to_cpu_octets
            .checked_add(pair_octets)
            .and_then(|value| value.checked_add(state_octets))
            .ok_or(CudaRelationError::ExtentOverflow)?;
        let mut relations = output_pairs
            .into_iter()
            .zip(output_states)
            .map(|(pair, state)| CudaClassifiedRelation { pair, state })
            .collect::<Vec<_>>();
        relations.sort();
        Ok((
            CudaSparseRelations { relations },
            CudaRelationReceipt {
                schema: "holonic-engine.cuda-exact-relation-receipt.v3".to_owned(),
                device: self.device_name.clone(),
                kernel_sha256: self.kernel_sha256.clone(),
                point_count: u64::from(point_count),
                relation_dimension: u64::from(front.dimension),
                classified_pairs: pair_count,
                returned_relations: positive_extent[0],
                cpu_to_device_octets,
                device_to_cpu_octets,
                launches,
                front_uploads,
                allocation_resizes,
            },
        ))
    }

    #[allow(clippy::too_many_arguments)]
    pub fn classify_positive_windows(
        &mut self,
        points: &[i64],
        point_count: u32,
        order: &[u32],
        windows: &[PackedRelationWindow],
        pair_count: u64,
        front: &PackedRelationFront,
    ) -> Result<(CudaSparseRelations, CudaRelationReceipt), CudaRelationError> {
        let (mut positive_count, mut negative_count) = self.validate(points, point_count, front)?;
        let point_extent =
            usize::try_from(point_count).map_err(|_| CudaRelationError::ExtentOverflow)?;
        if order.len() != point_extent {
            return Err(CudaRelationError::MalformedWindows);
        }
        let mut seen = vec![false; point_extent];
        for point in order {
            let point = usize::try_from(*point).map_err(|_| CudaRelationError::ExtentOverflow)?;
            let slot = seen
                .get_mut(point)
                .ok_or(CudaRelationError::MalformedWindows)?;
            if *slot {
                return Err(CudaRelationError::MalformedWindows);
            }
            *slot = true;
        }
        let mut expected_prefix = 0_u64;
        for window in windows {
            let end = usize::try_from(window.right_start)
                .map_err(|_| CudaRelationError::ExtentOverflow)?
                .checked_add(
                    usize::try_from(window.right_count)
                        .map_err(|_| CudaRelationError::ExtentOverflow)?,
                )
                .ok_or(CudaRelationError::ExtentOverflow)?;
            if window.prefix != expected_prefix
                || window.left >= point_count
                || window.right_count == 0
                || end > order.len()
            {
                return Err(CudaRelationError::MalformedWindows);
            }
            expected_prefix = expected_prefix
                .checked_add(u64::from(window.right_count))
                .ok_or(CudaRelationError::ExtentOverflow)?;
        }
        if expected_prefix != pair_count || (pair_count != 0 && windows.is_empty()) {
            return Err(CudaRelationError::MalformedWindows);
        }
        let window_count =
            u32::try_from(windows.len()).map_err(|_| CudaRelationError::ExtentOverflow)?;

        let (mut cpu_to_device_octets, mut allocation_resizes, front_uploads) =
            self.prepare_points_and_front(points, front)?;
        let order_resize = self.order.ensure(std::mem::size_of_val(order))?;
        let window_resize = self.windows.ensure(std::mem::size_of_val(windows))?;
        let counter_resize = self.counter.ensure(std::mem::size_of::<u64>())?;
        allocation_resizes = allocation_resizes
            .checked_add(order_resize)
            .and_then(|value| value.checked_add(window_resize))
            .and_then(|value| value.checked_add(counter_resize))
            .ok_or(CudaRelationError::ExtentOverflow)?;
        let order_octets = self.order.copy_from(order)?;
        let window_octets = self.windows.copy_from(windows)?;
        cpu_to_device_octets = cpu_to_device_octets
            .checked_add(order_octets)
            .and_then(|value| value.checked_add(window_octets))
            .ok_or(CudaRelationError::ExtentOverflow)?;
        let zero = [0_u64];
        cpu_to_device_octets = cpu_to_device_octets
            .checked_add(self.counter.copy_from(&zero)?)
            .ok_or(CudaRelationError::ExtentOverflow)?;

        let mut launches = 0_u64;
        if pair_count != 0 {
            let grid = u32::try_from(pair_count.div_ceil(u64::from(self.block_x)))
                .map_err(|_| CudaRelationError::ExtentOverflow)?;
            if grid > self.max_grid_x {
                return Err(CudaRelationError::ExtentOverflow);
            }
            let mut point_pointer = self.points.pointer;
            let mut order_pointer = self.order.pointer;
            let mut window_pointer = self.windows.pointer;
            let mut positive_pointer = self.positive_front.pointer;
            let mut negative_pointer = self.negative_front.pointer;
            let mut counter_pointer = self.counter.pointer;
            let mut window_count_argument = window_count;
            let mut dimension = front.dimension;
            let mut pair_count_argument = pair_count;
            let mut arguments = [
                (&mut point_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut order_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut window_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut positive_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut negative_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut counter_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut window_count_argument as *mut u32).cast::<c_void>(),
                (&mut dimension as *mut u32).cast::<c_void>(),
                (&mut positive_count as *mut u32).cast::<c_void>(),
                (&mut negative_count as *mut u32).cast::<c_void>(),
                (&mut pair_count_argument as *mut u64).cast::<c_void>(),
            ];
            // SAFETY: arguments match the compiled window-count signature.
            unsafe {
                driver(
                    cuLaunchKernel(
                        self.count_window_positive_function,
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
                    ),
                    "cuLaunchKernel(exact_relation_count_window_positive)",
                )?;
                driver(cuCtxSynchronize(), "cuCtxSynchronize")?;
            }
            launches = 1;
        }

        let mut positive_extent = [0_u64];
        let mut device_to_cpu_octets = self.counter.copy_to(&mut positive_extent)?;
        if positive_extent[0] > pair_count {
            return Err(CudaRelationError::MalformedSparseOutput);
        }
        let output_extent =
            usize::try_from(positive_extent[0]).map_err(|_| CudaRelationError::ExtentOverflow)?;
        if output_extent != 0 {
            let pair_resize = self.sparse_pairs.ensure(
                output_extent
                    .checked_mul(std::mem::size_of::<PackedRelationPair>())
                    .ok_or(CudaRelationError::ExtentOverflow)?,
            )?;
            let state_resize = self.sparse_states.ensure(output_extent)?;
            allocation_resizes = allocation_resizes
                .checked_add(pair_resize)
                .and_then(|value| value.checked_add(state_resize))
                .ok_or(CudaRelationError::ExtentOverflow)?;
            cpu_to_device_octets = cpu_to_device_octets
                .checked_add(self.counter.copy_from(&zero)?)
                .ok_or(CudaRelationError::ExtentOverflow)?;

            let grid = u32::try_from(pair_count.div_ceil(u64::from(self.block_x)))
                .map_err(|_| CudaRelationError::ExtentOverflow)?;
            if grid > self.max_grid_x {
                return Err(CudaRelationError::ExtentOverflow);
            }
            let mut point_pointer = self.points.pointer;
            let mut order_pointer = self.order.pointer;
            let mut window_pointer = self.windows.pointer;
            let mut positive_pointer = self.positive_front.pointer;
            let mut negative_pointer = self.negative_front.pointer;
            let mut output_pair_pointer = self.sparse_pairs.pointer;
            let mut output_state_pointer = self.sparse_states.pointer;
            let mut counter_pointer = self.counter.pointer;
            let mut window_count_argument = window_count;
            let mut dimension = front.dimension;
            let mut pair_count_argument = pair_count;
            let mut arguments = [
                (&mut point_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut order_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut window_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut positive_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut negative_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut output_pair_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut output_state_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut counter_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut window_count_argument as *mut u32).cast::<c_void>(),
                (&mut dimension as *mut u32).cast::<c_void>(),
                (&mut positive_count as *mut u32).cast::<c_void>(),
                (&mut negative_count as *mut u32).cast::<c_void>(),
                (&mut pair_count_argument as *mut u64).cast::<c_void>(),
            ];
            // SAFETY: arguments match the compiled window-emission signature.
            unsafe {
                driver(
                    cuLaunchKernel(
                        self.emit_window_positive_function,
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
                    ),
                    "cuLaunchKernel(exact_relation_emit_window_positive)",
                )?;
                driver(cuCtxSynchronize(), "cuCtxSynchronize")?;
            }
            launches = launches
                .checked_add(1)
                .ok_or(CudaRelationError::ExtentOverflow)?;
        }

        let mut emitted_extent = [0_u64];
        device_to_cpu_octets = device_to_cpu_octets
            .checked_add(self.counter.copy_to(&mut emitted_extent)?)
            .ok_or(CudaRelationError::ExtentOverflow)?;
        if emitted_extent != positive_extent {
            return Err(CudaRelationError::MalformedSparseOutput);
        }
        let mut output_pairs = vec![PackedRelationPair { left: 0, right: 0 }; output_extent];
        let mut output_states = vec![0_u8; output_extent];
        let pair_octets = self.sparse_pairs.copy_to(&mut output_pairs)?;
        let state_octets = self.sparse_states.copy_to(&mut output_states)?;
        device_to_cpu_octets = device_to_cpu_octets
            .checked_add(pair_octets)
            .and_then(|value| value.checked_add(state_octets))
            .ok_or(CudaRelationError::ExtentOverflow)?;
        let mut relations = output_pairs
            .into_iter()
            .zip(output_states)
            .map(|(pair, state)| CudaClassifiedRelation { pair, state })
            .collect::<Vec<_>>();
        relations.sort();
        Ok((
            CudaSparseRelations { relations },
            CudaRelationReceipt {
                schema: "holonic-engine.cuda-exact-relation-receipt.v3".to_owned(),
                device: self.device_name.clone(),
                kernel_sha256: self.kernel_sha256.clone(),
                point_count: u64::from(point_count),
                relation_dimension: u64::from(front.dimension),
                classified_pairs: pair_count,
                returned_relations: positive_extent[0],
                cpu_to_device_octets,
                device_to_cpu_octets,
                launches,
                front_uploads,
                allocation_resizes,
            },
        ))
    }

    pub fn grade_all_pairs_sparse(
        &mut self,
        points: &[i64],
        point_count: u32,
        membership: &[u64],
        front: &PackedRelationFront,
    ) -> Result<(CudaSparseGrade, CudaRelationReceipt), CudaRelationError> {
        let (mut positive_count, mut negative_count) = self.validate(points, point_count, front)?;
        if membership.len()
            != usize::try_from(point_count).map_err(|_| CudaRelationError::ExtentOverflow)?
        {
            return Err(CudaRelationError::MalformedMembership);
        }
        let pair_count = choose_two(u64::from(point_count))?;
        let (mut cpu_to_device_octets, mut allocation_resizes, front_uploads) =
            self.prepare_points_and_front(points, front)?;
        let membership_resize = self.membership.ensure(std::mem::size_of_val(membership))?;
        let counter_resize = self.counter.ensure(std::mem::size_of::<u64>())?;
        let grade_resize = self.grade_counts.ensure(8 * std::mem::size_of::<u64>())?;
        allocation_resizes = allocation_resizes
            .checked_add(membership_resize)
            .and_then(|value| value.checked_add(counter_resize))
            .and_then(|value| value.checked_add(grade_resize))
            .ok_or(CudaRelationError::ExtentOverflow)?;
        cpu_to_device_octets = cpu_to_device_octets
            .checked_add(self.membership.copy_from(membership)?)
            .ok_or(CudaRelationError::ExtentOverflow)?;
        let zero_count = [0_u64];
        let zero_grade = [0_u64; 8];
        let counter_octets = self.counter.copy_from(&zero_count)?;
        let grade_octets = self.grade_counts.copy_from(&zero_grade)?;
        cpu_to_device_octets = cpu_to_device_octets
            .checked_add(counter_octets)
            .and_then(|value| value.checked_add(grade_octets))
            .ok_or(CudaRelationError::ExtentOverflow)?;

        let mut launches = 0_u64;
        let grid = if pair_count == 0 {
            0
        } else {
            u32::try_from(
                pair_count.div_ceil(
                    u64::from(self.block_x)
                        .checked_mul(GRADE_ITEMS_PER_THREAD)
                        .ok_or(CudaRelationError::ExtentOverflow)?,
                ),
            )
            .map_err(|_| CudaRelationError::ExtentOverflow)?
        };
        if grid != 0 {
            let mut point_pointer = self.points.pointer;
            let mut positive_pointer = self.positive_front.pointer;
            let mut negative_pointer = self.negative_front.pointer;
            let mut membership_pointer = self.membership.pointer;
            let mut grade_pointer = self.grade_counts.pointer;
            let mut counter_pointer = self.counter.pointer;
            let mut point_count_argument = point_count;
            let mut dimension = front.dimension;
            let mut pair_count_argument = pair_count;
            let mut arguments = [
                (&mut point_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut positive_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut negative_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut membership_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut grade_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut counter_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut point_count_argument as *mut u32).cast::<c_void>(),
                (&mut dimension as *mut u32).cast::<c_void>(),
                (&mut positive_count as *mut u32).cast::<c_void>(),
                (&mut negative_count as *mut u32).cast::<c_void>(),
                (&mut pair_count_argument as *mut u64).cast::<c_void>(),
            ];
            // SAFETY: arguments match the compiled grade-reduction signature.
            unsafe {
                driver(
                    cuLaunchKernel(
                        self.grade_all_pairs_function,
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
                    ),
                    "cuLaunchKernel(exact_relation_grade_all_pairs)",
                )?;
                driver(cuCtxSynchronize(), "cuCtxSynchronize")?;
            }
            launches = 1;
        }

        let mut counts = [0_u64; 8];
        let mut obstruction_extent = [0_u64];
        let mut device_to_cpu_octets = self.grade_counts.copy_to(&mut counts)?;
        device_to_cpu_octets = device_to_cpu_octets
            .checked_add(self.counter.copy_to(&mut obstruction_extent)?)
            .ok_or(CudaRelationError::ExtentOverflow)?;
        if obstruction_extent[0] > pair_count {
            return Err(CudaRelationError::MalformedSparseOutput);
        }
        let output_extent = usize::try_from(obstruction_extent[0])
            .map_err(|_| CudaRelationError::ExtentOverflow)?;
        if output_extent != 0 {
            let pair_resize = self.sparse_pairs.ensure(
                output_extent
                    .checked_mul(std::mem::size_of::<PackedRelationPair>())
                    .ok_or(CudaRelationError::ExtentOverflow)?,
            )?;
            let state_resize = self.sparse_states.ensure(output_extent)?;
            allocation_resizes = allocation_resizes
                .checked_add(pair_resize)
                .and_then(|value| value.checked_add(state_resize))
                .ok_or(CudaRelationError::ExtentOverflow)?;
            cpu_to_device_octets = cpu_to_device_octets
                .checked_add(self.counter.copy_from(&zero_count)?)
                .ok_or(CudaRelationError::ExtentOverflow)?;
            let mut point_pointer = self.points.pointer;
            let mut positive_pointer = self.positive_front.pointer;
            let mut negative_pointer = self.negative_front.pointer;
            let mut membership_pointer = self.membership.pointer;
            let mut output_pair_pointer = self.sparse_pairs.pointer;
            let mut output_kind_pointer = self.sparse_states.pointer;
            let mut counter_pointer = self.counter.pointer;
            let mut point_count_argument = point_count;
            let mut dimension = front.dimension;
            let mut pair_count_argument = pair_count;
            let mut arguments = [
                (&mut point_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut positive_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut negative_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut membership_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut output_pair_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut output_kind_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut counter_pointer as *mut CuDevicePtr).cast::<c_void>(),
                (&mut point_count_argument as *mut u32).cast::<c_void>(),
                (&mut dimension as *mut u32).cast::<c_void>(),
                (&mut positive_count as *mut u32).cast::<c_void>(),
                (&mut negative_count as *mut u32).cast::<c_void>(),
                (&mut pair_count_argument as *mut u64).cast::<c_void>(),
            ];
            // SAFETY: arguments match the compiled sparse-obstruction signature.
            unsafe {
                driver(
                    cuLaunchKernel(
                        self.emit_grade_obstructions_function,
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
                    ),
                    "cuLaunchKernel(exact_relation_emit_grade_obstructions)",
                )?;
                driver(cuCtxSynchronize(), "cuCtxSynchronize")?;
            }
            launches = launches
                .checked_add(1)
                .ok_or(CudaRelationError::ExtentOverflow)?;
        }

        let mut emitted_extent = [0_u64];
        device_to_cpu_octets = device_to_cpu_octets
            .checked_add(self.counter.copy_to(&mut emitted_extent)?)
            .ok_or(CudaRelationError::ExtentOverflow)?;
        if emitted_extent != obstruction_extent {
            return Err(CudaRelationError::MalformedSparseOutput);
        }
        let mut output_pairs = vec![PackedRelationPair { left: 0, right: 0 }; output_extent];
        let mut output_kinds = vec![0_u8; output_extent];
        let pair_octets = self.sparse_pairs.copy_to(&mut output_pairs)?;
        let kind_octets = self.sparse_states.copy_to(&mut output_kinds)?;
        device_to_cpu_octets = device_to_cpu_octets
            .checked_add(pair_octets)
            .and_then(|value| value.checked_add(kind_octets))
            .ok_or(CudaRelationError::ExtentOverflow)?;
        let mut obstructions = output_pairs
            .into_iter()
            .zip(output_kinds)
            .map(|(pair, kind)| CudaRelationObstruction { pair, kind })
            .collect::<Vec<_>>();
        obstructions.sort();
        Ok((
            CudaSparseGrade {
                counts,
                obstructions,
            },
            CudaRelationReceipt {
                schema: "holonic-engine.cuda-exact-relation-receipt.v3".to_owned(),
                device: self.device_name.clone(),
                kernel_sha256: self.kernel_sha256.clone(),
                point_count: u64::from(point_count),
                relation_dimension: u64::from(front.dimension),
                classified_pairs: pair_count,
                returned_relations: obstruction_extent[0],
                cpu_to_device_octets,
                device_to_cpu_octets,
                launches,
                front_uploads,
                allocation_resizes,
            },
        ))
    }

    fn validate(
        &self,
        points: &[i64],
        point_count: u32,
        front: &PackedRelationFront,
    ) -> Result<(u32, u32), CudaRelationError> {
        let expected = usize::try_from(point_count)
            .map_err(|_| CudaRelationError::ExtentOverflow)?
            .checked_mul(
                usize::try_from(front.dimension).map_err(|_| CudaRelationError::ExtentOverflow)?,
            )
            .ok_or(CudaRelationError::ExtentOverflow)?;
        if points.len() != expected {
            return Err(CudaRelationError::MalformedPoints);
        }
        front.counts()
    }

    fn prepare_points_and_front(
        &mut self,
        points: &[i64],
        front: &PackedRelationFront,
    ) -> Result<(u64, u64, u64), CudaRelationError> {
        self.make_current()?;
        let mut allocation_resizes = self.points.ensure(std::mem::size_of_val(points))?;
        let mut cpu_to_device_octets = self.points.copy_from(points)?;
        let mut front_uploads = 0_u64;
        if self.resident_front.as_ref() != Some(front) {
            let positive_resize = self
                .positive_front
                .ensure(std::mem::size_of_val(front.positive_maxima.as_slice()))?;
            let negative_resize = self
                .negative_front
                .ensure(std::mem::size_of_val(front.negative_minima.as_slice()))?;
            allocation_resizes = allocation_resizes
                .checked_add(positive_resize)
                .and_then(|value| value.checked_add(negative_resize))
                .ok_or(CudaRelationError::ExtentOverflow)?;
            let positive_octets = self.positive_front.copy_from(&front.positive_maxima)?;
            let negative_octets = self.negative_front.copy_from(&front.negative_minima)?;
            cpu_to_device_octets = cpu_to_device_octets
                .checked_add(positive_octets)
                .and_then(|value| value.checked_add(negative_octets))
                .ok_or(CudaRelationError::ExtentOverflow)?;
            self.resident_front = Some(front.clone());
            front_uploads = 1;
        }
        Ok((cpu_to_device_octets, allocation_resizes, front_uploads))
    }

    #[allow(clippy::too_many_arguments)]
    fn classify(
        &mut self,
        points: &[i64],
        point_count: u32,
        pairs: Option<&[PackedRelationPair]>,
        front: &PackedRelationFront,
        mut positive_count: u32,
        mut negative_count: u32,
        output_extent: usize,
        pair_count_u64: u64,
    ) -> Result<(Vec<u8>, CudaRelationReceipt), CudaRelationError> {
        let (mut cpu_to_device_octets, mut allocation_resizes, front_uploads) =
            self.prepare_points_and_front(points, front)?;
        allocation_resizes = allocation_resizes
            .checked_add(self.output.ensure(output_extent)?)
            .ok_or(CudaRelationError::ExtentOverflow)?;

        let mut point_pointer = self.points.pointer;
        let mut positive_pointer = self.positive_front.pointer;
        let mut negative_pointer = self.negative_front.pointer;
        let mut output_pointer = self.output.pointer;
        let mut dimension = front.dimension;
        let mut point_count_argument = point_count;
        let mut launches = 0_u64;

        if output_extent != 0 {
            let grid = u32::try_from(pair_count_u64.div_ceil(u64::from(self.block_x)))
                .map_err(|_| CudaRelationError::ExtentOverflow)?;
            match pairs {
                None => {
                    let mut pair_count_argument = pair_count_u64;
                    let mut arguments = [
                        (&mut point_pointer as *mut CuDevicePtr).cast::<c_void>(),
                        (&mut positive_pointer as *mut CuDevicePtr).cast::<c_void>(),
                        (&mut negative_pointer as *mut CuDevicePtr).cast::<c_void>(),
                        (&mut output_pointer as *mut CuDevicePtr).cast::<c_void>(),
                        (&mut point_count_argument as *mut u32).cast::<c_void>(),
                        (&mut dimension as *mut u32).cast::<c_void>(),
                        (&mut positive_count as *mut u32).cast::<c_void>(),
                        (&mut negative_count as *mut u32).cast::<c_void>(),
                        (&mut pair_count_argument as *mut u64).cast::<c_void>(),
                    ];
                    // SAFETY: argument order and carriers match the compiled
                    // PTX signature, and all allocations outlive synchronize.
                    unsafe {
                        driver(
                            cuLaunchKernel(
                                self.all_pairs_function,
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
                            ),
                            "cuLaunchKernel(exact_relation_all_pairs)",
                        )?;
                    }
                }
                Some(pairs) => {
                    allocation_resizes = allocation_resizes
                        .checked_add(self.pairs.ensure(std::mem::size_of_val(pairs))?)
                        .ok_or(CudaRelationError::ExtentOverflow)?;
                    cpu_to_device_octets = cpu_to_device_octets
                        .checked_add(self.pairs.copy_from(pairs)?)
                        .ok_or(CudaRelationError::ExtentOverflow)?;
                    let mut pair_pointer = self.pairs.pointer;
                    let mut pair_count_argument = u32::try_from(pairs.len())
                        .map_err(|_| CudaRelationError::ExtentOverflow)?;
                    let mut arguments = [
                        (&mut point_pointer as *mut CuDevicePtr).cast::<c_void>(),
                        (&mut pair_pointer as *mut CuDevicePtr).cast::<c_void>(),
                        (&mut positive_pointer as *mut CuDevicePtr).cast::<c_void>(),
                        (&mut negative_pointer as *mut CuDevicePtr).cast::<c_void>(),
                        (&mut output_pointer as *mut CuDevicePtr).cast::<c_void>(),
                        (&mut pair_count_argument as *mut u32).cast::<c_void>(),
                        (&mut dimension as *mut u32).cast::<c_void>(),
                        (&mut positive_count as *mut u32).cast::<c_void>(),
                        (&mut negative_count as *mut u32).cast::<c_void>(),
                    ];
                    // SAFETY: as above; the pair allocation remains live
                    // through the synchronization inside this match arm.
                    unsafe {
                        driver(
                            cuLaunchKernel(
                                self.addressed_pairs_function,
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
                            ),
                            "cuLaunchKernel(exact_relation_addressed_pairs)",
                        )?;
                        driver(cuCtxSynchronize(), "cuCtxSynchronize")?;
                    }
                    launches = 1;
                }
            }
            if pairs.is_none() {
                // SAFETY: the active context owns the preceding launch.
                unsafe {
                    driver(cuCtxSynchronize(), "cuCtxSynchronize")?;
                }
                launches = 1;
            }
        }
        let mut states = vec![0_u8; output_extent];
        let device_to_cpu_octets = self.output.copy_to(&mut states)?;
        Ok((
            states,
            CudaRelationReceipt {
                schema: "holonic-engine.cuda-exact-relation-receipt.v2".to_owned(),
                device: self.device_name.clone(),
                kernel_sha256: self.kernel_sha256.clone(),
                point_count: u64::from(point_count),
                relation_dimension: u64::from(front.dimension),
                classified_pairs: pair_count_u64,
                returned_relations: pair_count_u64,
                cpu_to_device_octets,
                device_to_cpu_octets,
                launches,
                front_uploads,
                allocation_resizes,
            },
        ))
    }

    fn make_current(&self) -> Result<(), CudaRelationError> {
        // SAFETY: this executor owns the context, and its physical-law owner
        // serializes calls before making it current on the calling thread.
        unsafe { driver(cuCtxSetCurrent(self.context), "cuCtxSetCurrent") }
    }
}

impl Drop for CudaExactRelationExecutor {
    fn drop(&mut self) {
        // SAFETY: all handles are exclusively owned by this executor.  Device
        // storage must be released before its context is destroyed.
        unsafe {
            let _ = cuCtxSetCurrent(self.context);
            self.points.release();
            self.positive_front.release();
            self.negative_front.release();
            self.pairs.release();
            self.order.release();
            self.windows.release();
            self.output.release();
            self.membership.release();
            self.counter.release();
            self.grade_counts.release();
            self.sparse_pairs.release();
            self.sparse_states.release();
            let _ = cuModuleUnload(self.module);
            let _ = cuCtxDestroy_v2(self.context);
        }
    }
}

fn choose_two(extent: u64) -> Result<u64, CudaRelationError> {
    if extent < 2 {
        return Ok(0);
    }
    extent
        .checked_mul(extent - 1)
        .and_then(|value| value.checked_div(2))
        .ok_or(CudaRelationError::ExtentOverflow)
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum CudaRelationError {
    #[error("no CUDA device is visible")]
    NoDevice,
    #[error("CUDA {operation} failed: {name} ({code}) — {message}")]
    Driver {
        operation: &'static str,
        code: i32,
        name: String,
        message: String,
    },
    #[error("the exact packed relation front is malformed")]
    MalformedFront,
    #[error("the exact packed relation point carrier is malformed")]
    MalformedPoints,
    #[error("an addressed relation pair is malformed")]
    MalformedPair,
    #[error("an exact relation-window carrier is malformed")]
    MalformedWindows,
    #[error("an exact returned-partition membership carrier is malformed")]
    MalformedMembership,
    #[error("an exact sparse CUDA relation receipt has an impossible extent")]
    MalformedSparseOutput,
    #[error("an exact CUDA relation extent overflowed its device address carrier")]
    ExtentOverflow,
    #[error("an exact CUDA relation copy exceeded its retained device allocation")]
    AllocationExtent,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[ignore = "requires a CUDA device"]
    fn card_classifies_every_exact_pair_at_the_cpu_address() {
        let mut executor = CudaExactRelationExecutor::new().unwrap();
        let points = [0_i64, 0, 1, 1, 3, 0, 10, 10];
        let front = PackedRelationFront {
            dimension: 2,
            positive_maxima: vec![2, 2],
            negative_minima: vec![5, 5],
        };
        let (all, receipt) = executor.classify_all_pairs(&points, 4, &front).unwrap();
        assert_eq!(all, [0, 2, 1, 0, 1, 1]);
        assert_eq!(receipt.classified_pairs, 6);

        let pairs = [
            PackedRelationPair { left: 0, right: 1 },
            PackedRelationPair { left: 0, right: 3 },
        ];
        let (addressed, receipt) = executor
            .classify_addressed_pairs(&points, 4, &pairs, &front)
            .unwrap();
        assert_eq!(addressed, [0, 1]);
        assert_eq!(receipt.classified_pairs, 2);
        assert_eq!(receipt.front_uploads, 0);

        let every_pair = [
            PackedRelationPair { left: 0, right: 1 },
            PackedRelationPair { left: 0, right: 2 },
            PackedRelationPair { left: 0, right: 3 },
            PackedRelationPair { left: 1, right: 2 },
            PackedRelationPair { left: 1, right: 3 },
            PackedRelationPair { left: 2, right: 3 },
        ];
        let (positive, receipt) = executor
            .classify_positive_addressed_pairs(&points, 4, &every_pair, &front)
            .unwrap();
        assert_eq!(
            positive.relations,
            vec![
                CudaClassifiedRelation {
                    pair: every_pair[0],
                    state: 0,
                },
                CudaClassifiedRelation {
                    pair: every_pair[3],
                    state: 0,
                },
            ]
        );
        assert_eq!(receipt.classified_pairs, 6);
        assert_eq!(receipt.returned_relations, 2);
        assert_eq!(receipt.launches, 2);

        let windows = [
            PackedRelationWindow {
                prefix: 0,
                left: 0,
                right_start: 1,
                right_count: 1,
            },
            PackedRelationWindow {
                prefix: 1,
                left: 1,
                right_start: 2,
                right_count: 1,
            },
        ];
        let (window_positive, receipt) = executor
            .classify_positive_windows(&points, 4, &[0, 1, 2, 3], &windows, 2, &front)
            .unwrap();
        assert_eq!(window_positive, positive);
        assert_eq!(receipt.classified_pairs, 2);
        assert_eq!(receipt.returned_relations, 2);

        let (grade, receipt) = executor
            .grade_all_pairs_sparse(&points, 4, &[1, 1, 2, 2], &front)
            .unwrap();
        assert_eq!(grade.counts, [2, 4, 1, 2, 0, 1, 1, 0]);
        assert_eq!(
            grade.obstructions,
            vec![
                CudaRelationObstruction {
                    pair: every_pair[3],
                    kind: 2,
                },
                CudaRelationObstruction {
                    pair: every_pair[5],
                    kind: 0,
                },
            ]
        );
        assert_eq!(receipt.classified_pairs, 6);
        assert_eq!(receipt.returned_relations, 2);
        assert_eq!(receipt.launches, 2);
    }
}
