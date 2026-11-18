//! The safe typed layer over `ffi`. Every driver call is checked into a `Result` carrying the
//! driver's own error name + description; there are no panics on drop (Drop calls are best-effort).
use crate::ffi;
use core::ffi::{c_char, c_void};
use core::marker::PhantomData;
use std::ffi::CString;

// These two calls are the whole-machine boundary added after the original minimal FFI mouth.
// Keep them private: callers cross through the checked, typed wrappers below.
#[link(name = "cuda")]
unsafe extern "C" {
    fn cuDeviceGetAttribute(
        value: *mut i32,
        attribute: i32,
        device: ffi::CUdevice,
    ) -> ffi::CUresult;
    fn cuFuncGetAttribute(
        value: *mut i32,
        attribute: i32,
        function: ffi::CUfunction,
    ) -> ffi::CUresult;
}

/// A driver fault: the raw `CUresult`, its symbolic name, and its human description — all from
/// the driver itself via `cuGetErrorName`/`cuGetErrorString`. No interpretation, no scoring.
#[derive(Debug, Clone)]
pub struct CudaError {
    pub code: i32,
    pub name: String,
    pub message: String,
    /// The safe-layer call site that observed the fault.
    pub context: &'static str,
}

impl std::fmt::Display for CudaError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}: {} ({}) [{}]",
            self.context, self.name, self.code, self.message
        )
    }
}
impl std::error::Error for CudaError {}

pub type Result<T> = std::result::Result<T, CudaError>;

fn invalid_driver_value(context: &'static str, message: String) -> CudaError {
    CudaError {
        code: -1,
        name: String::from("INVALID_DRIVER_VALUE"),
        message,
        context,
    }
}

fn driver_string(f: unsafe extern "C" fn(i32, *mut *const c_char) -> i32, code: i32) -> String {
    let mut p: *const c_char = core::ptr::null();
    unsafe {
        if f(code, &mut p) == ffi::CUDA_SUCCESS && !p.is_null() {
            return core::ffi::CStr::from_ptr(p).to_string_lossy().into_owned();
        }
    }
    String::from("<no driver string>")
}

/// Turn a raw `CUresult` into a checked `Result`, tagging the observing call site.
fn check(code: i32, context: &'static str) -> Result<()> {
    if code == ffi::CUDA_SUCCESS {
        Ok(())
    } else {
        Err(CudaError {
            code,
            name: driver_string(ffi::cuGetErrorName, code),
            message: driver_string(ffi::cuGetErrorString, code),
            context,
        })
    }
}

/// Complete a synchronous host-to-device transfer before a consumer on an arbitrary
/// nonblocking stream may read it. CUDA permits a pageable-source `cuMemcpyHtoD_v2` to return
/// after staging the host bytes while the DMA continues; the legacy stream synchronization is
/// the narrow completion edge for that transfer. Explicit async copies keep their caller-owned
/// stream/event contract and do not use this helper.
unsafe fn copy_h_to_d_sync(
    destination: ffi::CUdeviceptr,
    source: *const c_void,
    bytes: usize,
    context: &'static str,
) -> Result<()> {
    // SAFETY: the caller guarantees `source` addresses `bytes` readable host bytes and
    // `destination` a device allocation of at least `bytes` in the current context.
    check(
        unsafe { ffi::cuMemcpyHtoD_v2(destination, source, bytes) },
        context,
    )?;
    check(
        unsafe { ffi::cuStreamSynchronize(core::ptr::null_mut()) },
        "cuStreamSynchronize(legacy host-to-device copy)",
    )
}

/// Initialise the driver. Idempotent; call once before anything else.
pub fn init() -> Result<()> {
    unsafe { check(ffi::cuInit(0), "cuInit") }
}

/// A physical device handle plus its driver-reported name.
#[derive(Debug, Clone)]
pub struct Device {
    pub handle: ffi::CUdevice,
    pub name: String,
}

/// A CUDA Driver API device-attribute number. `from_raw` keeps the checked wrapper generic while
/// the named constants pin the launch census to the stable CUDA ABI values it needs.
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DeviceAttribute(i32);

impl DeviceAttribute {
    pub const MAX_THREADS_PER_BLOCK: DeviceAttribute = DeviceAttribute(1);
    pub const MAX_GRID_DIM_X: DeviceAttribute = DeviceAttribute(5);
    pub const MAX_GRID_DIM_Y: DeviceAttribute = DeviceAttribute(6);
    pub const MAX_GRID_DIM_Z: DeviceAttribute = DeviceAttribute(7);
    pub const MAX_SHARED_MEMORY_PER_BLOCK: DeviceAttribute = DeviceAttribute(8);
    pub const WARP_SIZE: DeviceAttribute = DeviceAttribute(10);
    pub const MAX_REGISTERS_PER_BLOCK: DeviceAttribute = DeviceAttribute(12);
    pub const MULTIPROCESSOR_COUNT: DeviceAttribute = DeviceAttribute(16);
    pub const CONCURRENT_KERNELS: DeviceAttribute = DeviceAttribute(31);
    pub const MAX_THREADS_PER_MULTIPROCESSOR: DeviceAttribute = DeviceAttribute(39);
    pub const COMPUTE_CAPABILITY_MAJOR: DeviceAttribute = DeviceAttribute(75);
    pub const COMPUTE_CAPABILITY_MINOR: DeviceAttribute = DeviceAttribute(76);
    pub const MAX_SHARED_MEMORY_PER_MULTIPROCESSOR: DeviceAttribute = DeviceAttribute(81);
    pub const MAX_REGISTERS_PER_MULTIPROCESSOR: DeviceAttribute = DeviceAttribute(82);
    pub const COOPERATIVE_LAUNCH: DeviceAttribute = DeviceAttribute(95);
    pub const MAX_SHARED_MEMORY_PER_BLOCK_OPTIN: DeviceAttribute = DeviceAttribute(97);
    pub const MAX_BLOCKS_PER_MULTIPROCESSOR: DeviceAttribute = DeviceAttribute(106);
    pub const VIRTUAL_MEMORY_MANAGEMENT_SUPPORTED: DeviceAttribute = DeviceAttribute(102);

    pub const fn from_raw(value: i32) -> DeviceAttribute {
        DeviceAttribute(value)
    }

    pub const fn raw(self) -> i32 {
        self.0
    }
}

/// Driver-reported limits used to derive a production launch shape from the mounted card itself.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LaunchCensus {
    pub max_grid: Dim3,
    pub max_threads_per_block: u32,
    pub multiprocessor_count: u32,
}

impl Device {

    pub fn get(ordinal: i32) -> Result<Device> {
        let mut handle: ffi::CUdevice = 0;
        unsafe { check(ffi::cuDeviceGet(&mut handle, ordinal), "cuDeviceGet")? };
        let mut buf = [0i8; 256];
        unsafe {
            check(
                ffi::cuDeviceGetName(buf.as_mut_ptr() as *mut c_char, buf.len() as i32, handle),
                "cuDeviceGetName",
            )?
        };
        let name = unsafe { core::ffi::CStr::from_ptr(buf.as_ptr() as *const c_char) }
            .to_string_lossy()
            .into_owned();
        Ok(Device { handle, name })
    }

    /// Read any `CUdevice_attribute` through the checked driver boundary.
    pub fn attribute(&self, attribute: DeviceAttribute) -> Result<i32> {
        let mut value = 0;
        unsafe {
            check(
                cuDeviceGetAttribute(&mut value, attribute.raw(), self.handle),
                "cuDeviceGetAttribute",
            )?
        };
        Ok(value)
    }

    /// Read the card's launch-relevant extents without naming a card or imposing a utilization
    /// policy. A caller may derive its launch directly from this census.
    pub fn launch_census(&self) -> Result<LaunchCensus> {
        fn positive(value: i32, field: &'static str) -> Result<u32> {
            if value <= 0 {
                return Err(invalid_driver_value(
                    "Device::launch_census",
                    format!("driver reported {field}={value}; expected a positive extent"),
                ));
            }
            Ok(value as u32)
        }

        let max_grid = Dim3 {
            x: positive(
                self.attribute(DeviceAttribute::MAX_GRID_DIM_X)?,
                "max grid X",
            )?,
            y: positive(
                self.attribute(DeviceAttribute::MAX_GRID_DIM_Y)?,
                "max grid Y",
            )?,
            z: positive(
                self.attribute(DeviceAttribute::MAX_GRID_DIM_Z)?,
                "max grid Z",
            )?,
        };
        Ok(LaunchCensus {
            max_grid,
            max_threads_per_block: positive(
                self.attribute(DeviceAttribute::MAX_THREADS_PER_BLOCK)?,
                "max threads per block",
            )?,
            multiprocessor_count: positive(
                self.attribute(DeviceAttribute::MULTIPROCESSOR_COUNT)?,
                "multiprocessor count",
            )?,
        })
    }
}

/// A driver context bound to a device. Destroyed on drop (best-effort).
pub struct Context {
    ctx: ffi::CUcontext,
}

/// One declared ordered device current. Kernels launched through this owner are physically
/// ordered without synchronizing unrelated work in the complete CUDA context.
pub struct Stream {
    stream: ffi::CUstream,
}

impl Stream {
    pub fn create() -> Result<Self> {
        let mut stream = core::ptr::null_mut();
        unsafe {
            check(
                ffi::cuStreamCreate(&mut stream, 1),
                "cuStreamCreate(CU_STREAM_NON_BLOCKING)",
            )?
        };
        Ok(Self { stream })
    }

    pub fn synchronize(&self) -> Result<()> {
        unsafe { check(ffi::cuStreamSynchronize(self.stream), "cuStreamSynchronize") }
    }

    /// Set `count` 32-bit words at `pointer` to `value`, ordered on this stream (a memset node
    /// under capture).
    pub fn memset_u32_async(
        &self,
        pointer: ffi::CUdeviceptr,
        value: u32,
        count: usize,
    ) -> Result<()> {
        unsafe {
            check(
                ffi::cuMemsetD32Async(pointer, value, count, self.stream),
                "cuMemsetD32Async",
            )
        }
    }

    /// A device-to-device copy ordered on this stream (a memcpy node under capture). Nothing
    /// crosses the apparatus boundary.
    pub fn copy_device_to_device_async(
        &self,
        destination: ffi::CUdeviceptr,
        source: ffi::CUdeviceptr,
        bytes: usize,
    ) -> Result<()> {
        unsafe {
            check(
                ffi::cuMemcpyDtoDAsync_v2(destination, source, bytes, self.stream),
                "cuMemcpyDtoDAsync_v2",
            )
        }
    }
}

impl Drop for Stream {
    fn drop(&mut self) {
        if !self.stream.is_null() {
            unsafe {
                let _ = ffi::cuStreamDestroy_v2(self.stream);
            }
            self.stream = core::ptr::null_mut();
        }
    }
}

// CUDA's driver header names 0x04 `CU_CTX_SCHED_BLOCKING_SYNC`. Context scheduling belongs to
// the cpu apparatus: while a long kernel carries a real worldline, sleeping this boundary thread
// preserves a CPU core without changing device work or the construction crossing it.
const CU_CTX_SCHED_BLOCKING_SYNC: u32 = 0x04;

/// Memory visible to the current driver context at the instant of the read.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MemoryInfo {
    pub free_bytes: usize,
    pub total_bytes: usize,
}

impl Context {
    pub fn create(dev: &Device) -> Result<Context> {
        let mut ctx: ffi::CUcontext = core::ptr::null_mut();
        unsafe {
            check(
                ffi::cuCtxCreate_v2(&mut ctx, CU_CTX_SCHED_BLOCKING_SYNC, dev.handle),
                "cuCtxCreate_v2",
            )?
        };
        Ok(Context { ctx })
    }

    /// Make this retained context current on the calling cpu thread.
    ///
    /// CUDA's Driver API keeps current-context selection in thread-local apparatus. Independent
    /// exact executors may lawfully retain different contexts on one device, so an owner must
    /// reactivate its own context before touching any module, function, or allocation handle.
    pub fn make_current(&self) -> Result<()> {
        unsafe { check(ffi::cuCtxSetCurrent(self.ctx), "cuCtxSetCurrent") }
    }

    /// Read current free and total device memory directly from the driver.
    pub fn memory_info(&self) -> Result<MemoryInfo> {
        self.make_current()?;
        let mut free_bytes = 0;
        let mut total_bytes = 0;
        unsafe {
            check(
                ffi::cuMemGetInfo_v2(&mut free_bytes, &mut total_bytes),
                "cuMemGetInfo_v2",
            )?
        };
        if free_bytes > total_bytes {
            return Err(invalid_driver_value(
                "Context::memory_info",
                format!(
                    "driver reported free memory {free_bytes} above total memory {total_bytes}"
                ),
            ));
        }
        Ok(MemoryInfo {
            free_bytes,
            total_bytes,
        })
    }

}

// Driver JIT cleanup or another client can change the global free-memory reading between
// samples. Retry this small calibration, never a native operation, and still require the
// complete one-word/wider-allocation conservation check. No page size is guessed. Every
// discarded sample's own reading is retained and returned with the last, so the refusal shows
// whether the readings varied (a perturbed card) or repeated (an allocator that does not compose).

impl Drop for Context {
    fn drop(&mut self) {
        if !self.ctx.is_null() {
            unsafe {
                let _ = ffi::cuCtxDestroy_v2(self.ctx);
            }
        }
    }
}

/// A loaded module (a PTX image JIT-compiled by the driver). Unloaded on drop (best-effort).
pub struct Module {
    module: ffi::CUmodule,
    /// [realization; November 15] Each entry's handle, looked up once: a launch reads the handle the module already gave, where it
    /// had asked the driver again by a new C string at every launch (about 2,900 launches a section of the store line).
    functions: std::cell::RefCell<std::collections::HashMap<String, ffi::CUfunction>>,
}

impl Module {
    /// Load a PTX text image. The driver reads it as a NUL-terminated C string, so we copy and
    /// append a terminator (PTX artifacts from rustc carry no trailing NUL).
    pub fn load_ptx(ptx: &[u8]) -> Result<Module> {
        let mut image: Vec<u8> = Vec::with_capacity(ptx.len() + 1);
        image.extend_from_slice(ptx);
        if image.last() != Some(&0) {
            image.push(0);
        }
        let mut module: ffi::CUmodule = core::ptr::null_mut();
        unsafe {
            check(
                ffi::cuModuleLoadData(&mut module, image.as_ptr() as *const c_void),
                "cuModuleLoadData",
            )?
        };
        Ok(Module { module, functions: std::cell::RefCell::new(std::collections::HashMap::new()) })
    }

    pub fn function(&self, name: &str) -> Result<Function<'_>> {
        if let Some(&func) = self.functions.borrow().get(name) {
            return Ok(Function { func, _module: PhantomData });
        }
        let cname = CString::new(name).map_err(|_| CudaError {
            code: -1,
            name: String::from("BAD_NAME"),
            message: String::from("kernel name contained an interior NUL"),
            context: "Module::function",
        })?;
        let mut func: ffi::CUfunction = core::ptr::null_mut();
        unsafe {
            check(
                ffi::cuModuleGetFunction(&mut func, self.module, cname.as_ptr()),
                "cuModuleGetFunction",
            )?
        };
        self.functions.borrow_mut().insert(name.to_owned(), func);
        Ok(Function {
            func,
            _module: PhantomData,
        })
    }
}

impl Drop for Module {
    fn drop(&mut self) {
        if !self.module.is_null() {
            unsafe {
                let _ = ffi::cuModuleUnload(self.module);
            }
        }
    }
}

/// A kernel entry point. Borrows its module so it cannot outlive the loaded image.
pub struct Function<'m> {
    func: ffi::CUfunction,
    _module: PhantomData<&'m Module>,
}

/// A block/grid extent. Traversals may use X/Y; one-dimensional mouths leave Y/Z at one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Dim3 {
    pub x: u32,
    pub y: u32,
    pub z: u32,
}
impl Dim3 {
    pub fn x(x: u32) -> Dim3 {
        Dim3 { x, y: 1, z: 1 }
    }
}

impl Function<'_> {
    /// The driver's active blocks per multiprocessor for this lowered function and the exact
    /// block/shared surface offered to its cooperative launch. Zero means no resident block.
    pub fn active_blocks_per_multiprocessor(
        &self,
        threads: u32,
        shared_bytes: u32,
    ) -> Result<u32> {
        let threads = i32::try_from(threads)
            .ok()
            .filter(|n| *n > 0)
            .ok_or_else(|| {
                invalid_driver_value(
                    "Function::active_blocks_per_multiprocessor",
                    "a block has a positive signed-32-bit thread extent".into(),
                )
            })?;
        let mut blocks = 0;
        unsafe {
            check(
                ffi::cuOccupancyMaxActiveBlocksPerMultiprocessor(
                    &mut blocks,
                    self.func,
                    threads,
                    shared_bytes as usize,
                ),
                "cuOccupancyMaxActiveBlocksPerMultiprocessor",
            )?;
        }
        u32::try_from(blocks).map_err(|_| {
            invalid_driver_value(
                "Function::active_blocks_per_multiprocessor",
                "the driver reported negative occupancy".into(),
            )
        })
    }

    /// Read the driver/JIT's actual block limit for this entry, after PTX has been lowered for the
    /// mounted card. Attribute zero is `CU_FUNC_ATTRIBUTE_MAX_THREADS_PER_BLOCK`.
    pub fn max_threads_per_block(&self) -> Result<u32> {
        let mut value = 0i32;
        unsafe {
            check(
                cuFuncGetAttribute(&mut value, 0, self.func),
                "cuFuncGetAttribute(MAX_THREADS_PER_BLOCK)",
            )?
        };
        if value <= 0 {
            return Err(invalid_driver_value(
                "Function::max_threads_per_block",
                format!("driver reported a non-positive function block extent {value}"),
            ));
        }
        Ok(value as u32)
    }

    /// Read the driver/JIT's actual per-thread local-memory surface for this entry after PTX has
    /// been lowered for the mounted card. Attribute three is
    /// `CU_FUNC_ATTRIBUTE_LOCAL_SIZE_BYTES`. Zero is lawful for an entry which needs no local
    /// surface; a negative driver report is malformed.
    pub fn local_size_bytes(&self) -> Result<usize> {
        let mut value = 0i32;
        unsafe {
            check(
                cuFuncGetAttribute(&mut value, 3, self.func),
                "cuFuncGetAttribute(LOCAL_SIZE_BYTES)",
            )?
        };
        usize::try_from(value).map_err(|_| {
            invalid_driver_value(
                "Function::local_size_bytes",
                format!("driver reported a negative per-thread local extent {value}"),
            )
        })
    }

    /// Read the driver/JIT's actual per-thread register count for this entry after PTX has been
    /// lowered for the mounted card. Attribute four is `CU_FUNC_ATTRIBUTE_NUM_REGS`.
    ///
    /// **A measurement, never a governor.** The count is what the loaded module actually carries,
    /// so a caller deriving a residency candidate family from it is reading the apparatus rather
    /// than estimating it; nothing here chooses a geometry.
    pub fn num_regs(&self) -> Result<u32> {
        let mut value = 0i32;
        unsafe {
            check(
                cuFuncGetAttribute(&mut value, 4, self.func),
                "cuFuncGetAttribute(NUM_REGS)",
            )?
        };
        if value < 0 {
            return Err(invalid_driver_value(
                "Function::num_regs",
                format!("driver reported a negative per-thread register count {value}"),
            ));
        }
        Ok(value as u32)
    }

    /// The statically declared shared surface of this entry, in octets. Attribute one is
    /// `CU_FUNC_ATTRIBUTE_SHARED_SIZE_BYTES`; it excludes the dynamic extent a launch declares.
    pub fn static_shared_bytes(&self) -> Result<u32> {
        let mut value = 0i32;
        unsafe {
            check(
                cuFuncGetAttribute(&mut value, 1, self.func),
                "cuFuncGetAttribute(SHARED_SIZE_BYTES)",
            )?
        };
        if value < 0 {
            return Err(invalid_driver_value(
                "Function::static_shared_bytes",
                format!("driver reported a negative static shared extent {value}"),
            ));
        }
        Ok(value as u32)
    }

    /// Launch on a stream with `shared_bytes` of dynamic shared memory per block — a block
    /// reduction's own working surface, sized by the caller from the extent it reduces.
    pub fn launch_on_shared(
        &self,
        stream: &Stream,
        grid: Dim3,
        block: Dim3,
        shared_bytes: u32,
        params: &mut [*mut c_void],
    ) -> Result<()> {
        self.launch_raw(grid, block, shared_bytes, stream.stream, params)
    }

    fn launch_raw(
        &self,
        grid: Dim3,
        block: Dim3,
        shared_bytes: u32,
        stream: ffi::CUstream,
        params: &mut [*mut c_void],
    ) -> Result<()> {
        unsafe {
            check(
                ffi::cuLaunchKernel(
                    self.func,
                    grid.x,
                    grid.y,
                    grid.z,
                    block.x,
                    block.y,
                    block.z,
                    shared_bytes,
                    stream,
                    params.as_mut_ptr(),
                    core::ptr::null_mut(),
                ),
                "cuLaunchKernel",
            )
        }
    }
}

/// A typed device allocation of `len` elements of `T`. Freed on drop (best-effort).
/// `T` must be a plain-old-data value type (`u32`/`u64` here); the smoke uses exactly those.
pub struct DeviceBuffer<T> {
    ptr: ffi::CUdeviceptr,
    len: usize,
    _marker: PhantomData<T>,
}

/// A device element type whose valid zero value is an integral number of zeroed CUDA dwords.
///
/// # Safety
///
/// Implementors must accept an all-zero bit pattern as a valid value, and their size must be a
/// non-zero multiple of `u32`'s size.
pub unsafe trait DeviceZeroable: Copy {}

unsafe impl DeviceZeroable for u32 {}
unsafe impl DeviceZeroable for u64 {}
unsafe impl DeviceZeroable for i64 {}
unsafe impl DeviceZeroable for i128 {}

pub fn device_dword_count<T: DeviceZeroable>(len: usize) -> usize {
    let bytes = len
        .checked_mul(core::mem::size_of::<T>())
        .expect("byte size overflow");
    debug_assert_ne!(core::mem::size_of::<T>(), 0);
    debug_assert_eq!(bytes % core::mem::size_of::<u32>(), 0);
    bytes / core::mem::size_of::<u32>()
}

impl<T: Copy> DeviceBuffer<T> {
    pub fn alloc(len: usize) -> Result<DeviceBuffer<T>> {
        let bytes = len
            .checked_mul(core::mem::size_of::<T>())
            .expect("byte size overflow");
        let mut ptr: ffi::CUdeviceptr = 0;
        unsafe { check(ffi::cuMemAlloc_v2(&mut ptr, bytes), "cuMemAlloc_v2")? };
        Ok(DeviceBuffer {
            ptr,
            len,
            _marker: PhantomData,
        })
    }

    /// The raw device address, for passing as a kernel argument.
    pub fn device_ptr(&self) -> ffi::CUdeviceptr {
        self.ptr
    }

    /// Write one exact subspan while leaving the rest of the reservation untouched.
    pub fn copy_range_from_slice(&self, offset: usize, src: &[T]) -> Result<()> {
        let end = offset.checked_add(src.len()).ok_or_else(|| {
            invalid_driver_value(
                "DeviceBuffer::copy_range_from_slice",
                "range overflow".into(),
            )
        })?;
        if end > self.len {
            return Err(invalid_driver_value(
                "DeviceBuffer::copy_range_from_slice",
                format!(
                    "range {offset}..{end} exceeds allocation length {}",
                    self.len
                ),
            ));
        }
        let byte_offset = offset
            .checked_mul(core::mem::size_of::<T>())
            .ok_or_else(|| {
                invalid_driver_value(
                    "DeviceBuffer::copy_range_from_slice",
                    "byte offset overflow".into(),
                )
            })?;
        let bytes = src
            .len()
            .checked_mul(core::mem::size_of::<T>())
            .ok_or_else(|| {
                invalid_driver_value(
                    "DeviceBuffer::copy_range_from_slice",
                    "byte length overflow".into(),
                )
            })?;
        let byte_offset = u64::try_from(byte_offset).map_err(|_| {
            invalid_driver_value(
                "DeviceBuffer::copy_range_from_slice",
                "byte offset exceeds the CUDA address wire".into(),
            )
        })?;
        let destination = self.ptr.checked_add(byte_offset).ok_or_else(|| {
            invalid_driver_value(
                "DeviceBuffer::copy_range_from_slice",
                "device address overflow".into(),
            )
        })?;
        unsafe {
            copy_h_to_d_sync(
                destination,
                src.as_ptr() as *const c_void,
                bytes,
                "cuMemcpyHtoD_v2(range)",
            )
        }
    }

    /// Read one exact subspan without staging the allocation's unused reservation tail.
    pub fn copy_range_to_slice(&self, offset: usize, dst: &mut [T]) -> Result<()> {
        let end = offset.checked_add(dst.len()).ok_or_else(|| {
            invalid_driver_value("DeviceBuffer::copy_range_to_slice", "range overflow".into())
        })?;
        if end > self.len {
            return Err(invalid_driver_value(
                "DeviceBuffer::copy_range_to_slice",
                format!(
                    "range {offset}..{end} exceeds allocation length {}",
                    self.len
                ),
            ));
        }
        let byte_offset = offset
            .checked_mul(core::mem::size_of::<T>())
            .ok_or_else(|| {
                invalid_driver_value(
                    "DeviceBuffer::copy_range_to_slice",
                    "byte offset overflow".into(),
                )
            })?;
        let bytes = dst
            .len()
            .checked_mul(core::mem::size_of::<T>())
            .ok_or_else(|| {
                invalid_driver_value(
                    "DeviceBuffer::copy_range_to_slice",
                    "byte length overflow".into(),
                )
            })?;
        let byte_offset = u64::try_from(byte_offset).map_err(|_| {
            invalid_driver_value(
                "DeviceBuffer::copy_range_to_slice",
                "byte offset exceeds the CUDA address wire".into(),
            )
        })?;
        let source = self.ptr.checked_add(byte_offset).ok_or_else(|| {
            invalid_driver_value(
                "DeviceBuffer::copy_range_to_slice",
                "device address overflow".into(),
            )
        })?;
        unsafe {
            check(
                ffi::cuMemcpyDtoH_v2(dst.as_mut_ptr() as *mut c_void, source, bytes),
                "cuMemcpyDtoH_v2(range)",
            )
        }
    }

}

impl<T> Drop for DeviceBuffer<T> {
    fn drop(&mut self) {
        if self.ptr != 0 {
            unsafe {
                let _ = ffi::cuMemFree_v2(self.ptr);
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn launch_census_attribute_numbers_match_the_cuda_driver_abi() {
        assert_eq!(DeviceAttribute::MAX_THREADS_PER_BLOCK.raw(), 1);
        assert_eq!(DeviceAttribute::MAX_GRID_DIM_X.raw(), 5);
        assert_eq!(DeviceAttribute::MAX_GRID_DIM_Y.raw(), 6);
        assert_eq!(DeviceAttribute::MAX_GRID_DIM_Z.raw(), 7);
        assert_eq!(DeviceAttribute::MULTIPROCESSOR_COUNT.raw(), 16);
        assert_eq!(
            DeviceAttribute::VIRTUAL_MEMORY_MANAGEMENT_SUPPORTED.raw(),
            102
        );
        // The hardware-law census (`hnn::card::DeviceCensus`), against `cuda.h`'s
        // `CUdevice_attribute`.
        assert_eq!(DeviceAttribute::MAX_SHARED_MEMORY_PER_BLOCK.raw(), 8);
        assert_eq!(DeviceAttribute::WARP_SIZE.raw(), 10);
        assert_eq!(DeviceAttribute::MAX_REGISTERS_PER_BLOCK.raw(), 12);
        assert_eq!(DeviceAttribute::MAX_THREADS_PER_MULTIPROCESSOR.raw(), 39);
        assert_eq!(DeviceAttribute::COMPUTE_CAPABILITY_MAJOR.raw(), 75);
        assert_eq!(DeviceAttribute::COMPUTE_CAPABILITY_MINOR.raw(), 76);
        assert_eq!(
            DeviceAttribute::MAX_SHARED_MEMORY_PER_MULTIPROCESSOR.raw(),
            81
        );
        assert_eq!(DeviceAttribute::MAX_REGISTERS_PER_MULTIPROCESSOR.raw(), 82);
        assert_eq!(DeviceAttribute::COOPERATIVE_LAUNCH.raw(), 95);
        assert_eq!(DeviceAttribute::MAX_SHARED_MEMORY_PER_BLOCK_OPTIN.raw(), 97);
        assert_eq!(DeviceAttribute::MAX_BLOCKS_PER_MULTIPROCESSOR.raw(), 106);
        assert_eq!(DeviceAttribute::from_raw(123).raw(), 123);
    }

    #[test]
    fn zero_fill_count_is_measured_in_cuda_dwords() {
        assert_eq!(device_dword_count::<u32>(7), 7);
        assert_eq!(device_dword_count::<u64>(7), 14);
    }
}
