//! The safe typed layer over `ffi`. Every driver call is checked into a `Result` carrying the
//! driver's own error name + description; there are no panics on drop (Drop calls are best-effort).
use crate::ffi;
use core::ffi::{c_char, c_void};
use core::marker::PhantomData;
use std::ffi::CString;

// These three calls are the whole-machine boundary added after the original minimal FFI mouth.
// Keep them private: callers cross through the checked, typed wrappers below.
#[link(name = "cuda")]
extern "C" {
    fn cuMemsetD32_v2(dst_device: ffi::CUdeviceptr, value: u32, count: usize) -> ffi::CUresult;
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
    pub const MULTIPROCESSOR_COUNT: DeviceAttribute = DeviceAttribute(16);
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
    pub fn count() -> Result<i32> {
        let mut n = 0;
        unsafe { check(ffi::cuDeviceGetCount(&mut n), "cuDeviceGetCount")? };
        Ok(n)
    }

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

    /// This owner is formed only through `CU_STREAM_NON_BLOCKING`; expose that physical contract
    /// so production receipts need not infer it from an implementation constant.
    pub const fn is_nonblocking(&self) -> bool {
        true
    }

    /// Order this stream's later work after an event: a dependency edge, not a cpu wait. Under
    /// capture it becomes a graph edge and nothing blocks.
    pub fn wait_event(&self, event: &Event) -> Result<()> {
        unsafe { check(ffi::cuStreamWaitEvent(self.stream, event.event, 0), "cuStreamWaitEvent") }
    }

    /// Begin recording every launch, event, memset and copy issued to this stream — and to any
    /// stream that waits on an event recorded in it — as one graph, instead of executing them.
    /// `CU_STREAM_CAPTURE_MODE_THREAD_LOCAL` (1): the capturing thread may issue no potentially
    /// synchronizing apparatus call (an allocation, a synchronous copy) until the capture ends —
    /// so a capture cannot silently interleave one — while other threads of the process, each
    /// with its own exact owner, are unaffected.
    pub fn begin_capture(&self) -> Result<()> {
        unsafe { check(ffi::cuStreamBeginCapture_v2(self.stream, 1), "cuStreamBeginCapture_v2") }
    }

    /// Close the capture and return the bound graph. Every forked stream must have been joined
    /// back through an event this stream waited on; the driver refuses an unjoined capture.
    pub fn end_capture(&self) -> Result<Graph> {
        let mut graph: ffi::CUgraph = core::ptr::null_mut();
        unsafe { check(ffi::cuStreamEndCapture(self.stream, &mut graph), "cuStreamEndCapture")? };
        Ok(Graph { graph })
    }

    /// Set `count` 32-bit words at `pointer` to `value`, ordered on this stream (a memset node
    /// under capture).
    pub fn memset_u32_async(&self, pointer: ffi::CUdeviceptr, value: u32, count: usize) -> Result<()> {
        unsafe { check(ffi::cuMemsetD32Async(pointer, value, count, self.stream), "cuMemsetD32Async") }
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

/// One recorded point on a stream, for ordering other streams after it. Created without timing,
/// so it is a dependency and never a clock.
pub struct Event {
    event: ffi::CUevent,
}

impl Event {
    /// `CU_EVENT_DISABLE_TIMING` (2): an event that orders and does not time.
    pub fn create() -> Result<Self> {
        let mut event: ffi::CUevent = core::ptr::null_mut();
        unsafe { check(ffi::cuEventCreate(&mut event, 2), "cuEventCreate(DISABLE_TIMING)")? };
        Ok(Self { event })
    }

    /// Record this event at the current tail of `stream`.
    pub fn record(&self, stream: &Stream) -> Result<()> {
        unsafe { check(ffi::cuEventRecord(self.event, stream.stream), "cuEventRecord") }
    }
}

impl Drop for Event {
    fn drop(&mut self) {
        if !self.event.is_null() {
            unsafe {
                let _ = ffi::cuEventDestroy_v2(self.event);
            }
            self.event = core::ptr::null_mut();
        }
    }
}

/// The census of a bound graph, read back from the driver: what the apparatus actually holds,
/// not what the caller intended to capture. `edges` is the dependency population; two nodes with
/// no path between them are co-present on the apparatus by construction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GraphCensus {
    pub nodes: usize,
    pub edges: usize,
    pub kernel_nodes: usize,
    pub memset_nodes: usize,
    pub memcpy_nodes: usize,
    pub other_nodes: usize,
}

/// A captured graph: the complete dependency structure of a deed, bound before it is launched.
pub struct Graph {
    graph: ffi::CUgraph,
}

impl Graph {
    /// Read the node and edge populations back from the driver.
    pub fn census(&self) -> Result<GraphCensus> {
        let mut nodes = 0usize;
        unsafe {
            check(
                ffi::cuGraphGetNodes(self.graph, core::ptr::null_mut(), &mut nodes),
                "cuGraphGetNodes(count)",
            )?
        };
        let mut handles: Vec<ffi::CUgraphNode> = vec![core::ptr::null_mut(); nodes];
        if nodes > 0 {
            unsafe {
                check(
                    ffi::cuGraphGetNodes(self.graph, handles.as_mut_ptr(), &mut nodes),
                    "cuGraphGetNodes",
                )?
            };
        }
        let mut edges = 0usize;
        unsafe {
            check(
                ffi::cuGraphGetEdges(self.graph, core::ptr::null_mut(), core::ptr::null_mut(), &mut edges),
                "cuGraphGetEdges(count)",
            )?
        };
        let (mut kernel_nodes, mut memset_nodes, mut memcpy_nodes, mut other_nodes) = (0, 0, 0, 0);
        for handle in handles.iter().take(nodes) {
            let mut kind: core::ffi::c_int = -1;
            unsafe { check(ffi::cuGraphNodeGetType(*handle, &mut kind), "cuGraphNodeGetType")? };
            // CUgraphNodeType: KERNEL 0, MEMCPY 1, MEMSET 2; everything else is counted apart.
            match kind {
                0 => kernel_nodes += 1,
                1 => memcpy_nodes += 1,
                2 => memset_nodes += 1,
                _ => other_nodes += 1,
            }
        }
        Ok(GraphCensus {
            nodes,
            edges,
            kernel_nodes,
            memset_nodes,
            memcpy_nodes,
            other_nodes,
        })
    }

    /// Instantiate the graph for launch. Flags 0: no device-launch, no auto-free.
    pub fn instantiate(&self) -> Result<GraphExec> {
        let mut exec: ffi::CUgraphExec = core::ptr::null_mut();
        unsafe {
            check(
                ffi::cuGraphInstantiateWithFlags(&mut exec, self.graph, 0),
                "cuGraphInstantiateWithFlags",
            )?
        };
        Ok(GraphExec { exec })
    }
}

impl Drop for Graph {
    fn drop(&mut self) {
        if !self.graph.is_null() {
            unsafe {
                let _ = ffi::cuGraphDestroy(self.graph);
            }
            self.graph = core::ptr::null_mut();
        }
    }
}

/// An instantiated graph. One `launch` enacts the whole bound structure; the cpu takes no part
/// between its nodes.
pub struct GraphExec {
    exec: ffi::CUgraphExec,
}

impl GraphExec {
    pub fn launch(&self, stream: &Stream) -> Result<()> {
        unsafe { check(ffi::cuGraphLaunch(self.exec, stream.stream), "cuGraphLaunch") }
    }
}

impl Drop for GraphExec {
    fn drop(&mut self) {
        if !self.exec.is_null() {
            unsafe {
                let _ = ffi::cuGraphExecDestroy(self.exec);
            }
            self.exec = core::ptr::null_mut();
        }
    }
}

/// A context this crate did NOT create and must not destroy: another owner mounted it and this
/// caller only makes it current. A borrowed context is how two exact owners share one device
/// context without either creating a second census of the card.
pub struct BorrowedContext {
    ctx: ffi::CUcontext,
}

impl BorrowedContext {
    /// Adopt a raw driver context handle. The caller asserts the owning body outlives every use.
    pub fn adopt(raw: *mut c_void) -> Result<Self> {
        if raw.is_null() {
            return Err(invalid_driver_value("BorrowedContext::adopt", "a null context handle".into()));
        }
        Ok(Self { ctx: raw })
    }

    pub fn make_current(&self) -> Result<()> {
        unsafe { check(ffi::cuCtxSetCurrent(self.ctx), "cuCtxSetCurrent") }
    }

    /// The raw handle, for equality against another owner's handle. Never dereferenced here.
    pub fn raw(&self) -> *mut c_void {
        self.ctx
    }

    /// Free and total device memory as the driver reports it for the current context.
    pub fn memory_info(&self) -> Result<MemoryInfo> {
        self.make_current()?;
        let mut free_bytes = 0;
        let mut total_bytes = 0;
        unsafe { check(ffi::cuMemGetInfo_v2(&mut free_bytes, &mut total_bytes), "cuMemGetInfo_v2")? };
        Ok(MemoryInfo { free_bytes, total_bytes })
    }

    /// The measured `cuMemAlloc` charge grain in this borrowed context — the same probe as
    /// [`Context::allocation_grain_bytes`], so an adopting owner can price its allocations against
    /// the grain the card actually charges.
    pub fn allocation_grain_bytes(&self) -> Result<usize> {
        self.make_current()?;
        measure_allocation_grain(|| self.memory_info())
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
/// CUDA Driver ABI value for `CU_LIMIT_STACK_SIZE`: per-thread device stack bytes.
const CU_LIMIT_STACK_SIZE: i32 = 0;

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

    /// Block until all preceding work on this context's default stream has completed.
    pub fn synchronize(&self) -> Result<()> {
        self.make_current()?;
        unsafe { check(ffi::cuCtxSynchronize(), "cuCtxSynchronize") }
    }

    /// Read the live context's per-thread device stack reservation.
    pub fn stack_limit_bytes(&self) -> Result<usize> {
        self.make_current()?;
        let mut bytes = 0usize;
        unsafe {
            check(
                ffi::cuCtxGetLimit(&mut bytes, CU_LIMIT_STACK_SIZE),
                "cuCtxGetLimit(CU_LIMIT_STACK_SIZE)",
            )?
        };
        Ok(bytes)
    }

    /// Ensure the context can carry the compiled entry's driver-reported per-thread local face.
    /// CUDA may round the request to its physical allocation grain; the post-read is authoritative.
    pub fn ensure_stack_limit_bytes(&self, required: usize) -> Result<usize> {
        if required == 0 {
            return self.stack_limit_bytes();
        }
        let before = self.stack_limit_bytes()?;
        if before < required {
            unsafe {
                check(
                    ffi::cuCtxSetLimit(CU_LIMIT_STACK_SIZE, required),
                    "cuCtxSetLimit(CU_LIMIT_STACK_SIZE)",
                )?
            };
        }
        let after = self.stack_limit_bytes()?;
        if after < required {
            return Err(invalid_driver_value(
                "Context::ensure_stack_limit_bytes",
                format!(
                    "driver retained stack limit {after} below compiled requirement {required}"
                ),
            ));
        }
        Ok(after)
    }

    /// Synchronize and explicitly destroy this context, reporting either CUDA failure to the
    /// caller. The raw handle is removed before the destroy call, so consuming this value leaves
    /// `Drop` with no handle to destroy a second time even when CUDA reports a teardown fault.
    pub fn destroy(mut self) -> Result<()> {
        if self.ctx.is_null() {
            return Err(invalid_driver_value(
                "Context::destroy",
                "context handle was already absent".into(),
            ));
        }

        let synchronized = self.synchronize();
        let ctx = core::mem::replace(&mut self.ctx, core::ptr::null_mut());
        let destroyed = unsafe { check(ffi::cuCtxDestroy_v2(ctx), "cuCtxDestroy_v2") };

        match (synchronized, destroyed) {
            (Ok(()), Ok(())) => Ok(()),
            (Err(error), Ok(())) | (Ok(()), Err(error)) => Err(error),
            (Err(sync), Err(mut destroy)) => {
                destroy.message = format!(
                    "{}; preceding synchronization also failed: {} ({}) [{}]",
                    destroy.message, sync.name, sync.code, sync.message,
                );
                Err(destroy)
            }
        }
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

    /// Measure the legacy `cuMemAlloc` charge directly in the live context. Production uses this
    /// substrate grain only to reserve simultaneous allocations before launch; it is not a body
    /// extent. A second probe proves the charge composes instead of assuming a page size.
    pub fn allocation_grain_bytes(&self) -> Result<usize> {
        measure_allocation_grain(|| self.memory_info())
    }
}

/// The allocation-grain probe shared by an owned and a borrowed context: one word's charge, then a
/// probe one word wider than that charge must cost exactly twice, and the free extent must close
/// after each. **Measured, never declared** — an apparatus coordinate a deed's admission rounds
/// every allocation up to.
fn measure_allocation_grain(memory_info: impl Fn() -> Result<MemoryInfo>) -> Result<usize> {
    let before = memory_info()?.free_bytes;
    let one = DeviceBuffer::<u32>::alloc(1)?;
    let after_one = memory_info()?.free_bytes;
    let grain = before.checked_sub(after_one).ok_or_else(|| {
        invalid_driver_value(
            "allocation_grain_bytes",
            "a live allocation increased reported free memory".into(),
        )
    })?;
    drop(one);
    let restored = memory_info()?.free_bytes;
    if grain == 0 || grain % core::mem::size_of::<u32>() != 0 || restored != before {
        return Err(invalid_driver_value(
            "allocation_grain_bytes",
            format!(
                "one-word charge {grain} and restored free extent {restored} do not close at {before}"
            ),
        ));
    }

    let wider_words = grain / core::mem::size_of::<u32>() + 1;
    let wider = DeviceBuffer::<u32>::alloc(wider_words)?;
    let after_wider = memory_info()?.free_bytes;
    let wider_charge = before.checked_sub(after_wider).ok_or_else(|| {
        invalid_driver_value(
            "allocation_grain_bytes",
            "the wider probe increased reported free memory".into(),
        )
    })?;
    drop(wider);
    let restored_again = memory_info()?.free_bytes;
    if grain.checked_mul(2) != Some(wider_charge) || restored_again != before {
        return Err(invalid_driver_value(
            "allocation_grain_bytes",
            format!(
                "the measured charge does not compose: grain {grain}, wider charge {wider_charge}, restored {restored_again}/{before}"
            ),
        ));
    }
    Ok(grain)
}

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
        Ok(Module { module })
    }

    pub fn function(&self, name: &str) -> Result<Function<'_>> {
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

/// One exact two-dimensional lowering of a flat invocation extent. `x_stride` is carried to the
/// kernel so Y continues the same flat surface; every field comes from the function/device mouths.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LinearLaunch {
    pub grid: Dim3,
    pub block: Dim3,
    pub x_stride: u32,
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

    /// Cover one flat work extent through X/Y using only driver-reported apertures. The u32
    /// `x_stride` is the kernel wire's declared boundary; a larger construction must be sharded by
    /// its conductor rather than clipped here.
    pub fn linear_launch(&self, census: LaunchCensus, work: u64) -> Result<LinearLaunch> {
        if work == 0 {
            return Err(invalid_driver_value(
                "Function::linear_launch",
                "a launch carries one positive invocation extent".into(),
            ));
        }
        let block_x = self
            .max_threads_per_block()?
            .min(census.max_threads_per_block);
        let blocks = work.div_ceil(block_x as u64);
        let stride_blocks = u32::MAX / block_x;
        let grid_x = blocks
            .min(census.max_grid.x as u64)
            .min(stride_blocks as u64) as u32;
        if grid_x == 0 {
            return Err(invalid_driver_value(
                "Function::linear_launch",
                "the function/device affords no X block".into(),
            ));
        }
        let grid_y = blocks.div_ceil(grid_x as u64);
        if grid_y > census.max_grid.y as u64 {
            return Err(invalid_driver_value(
                "Function::linear_launch",
                format!(
                    "work extent {work} exceeds the declared X/Y launch aperture {}x{} at block {block_x}",
                    census.max_grid.x, census.max_grid.y
                ),
            ));
        }
        Ok(LinearLaunch {
            grid: Dim3 {
                x: grid_x,
                y: grid_y as u32,
                z: 1,
            },
            block: Dim3::x(block_x),
            x_stride: grid_x * block_x,
        })
    }

    /// Cover one flat work extent with one complete CUDA block per work item. The caller derives
    /// `block_x` from the cooperative construction it is realizing; this boundary only proves that
    /// the function, device, and X/Y grid can carry it without clipping.
    pub fn block_launch(
        &self,
        census: LaunchCensus,
        work: u64,
        block_x: u32,
    ) -> Result<LinearLaunch> {
        if work == 0 || block_x == 0 {
            return Err(invalid_driver_value(
                "Function::block_launch",
                "a block surface carries positive work and a positive cooperative extent".into(),
            ));
        }
        let function_limit = self.max_threads_per_block()?;
        if block_x > function_limit || block_x > census.max_threads_per_block {
            return Err(invalid_driver_value(
                "Function::block_launch",
                format!(
                    "cooperative extent {block_x} exceeds function/device limits {function_limit}/{}",
                    census.max_threads_per_block,
                ),
            ));
        }
        let grid_x = work.min(census.max_grid.x as u64) as u32;
        if grid_x == 0 {
            return Err(invalid_driver_value(
                "Function::block_launch",
                "the function/device affords no X block".into(),
            ));
        }
        let grid_y = work.div_ceil(grid_x as u64);
        if grid_y > census.max_grid.y as u64 {
            return Err(invalid_driver_value(
                "Function::block_launch",
                format!(
                    "block work extent {work} exceeds the declared X/Y launch aperture {}x{}",
                    census.max_grid.x, census.max_grid.y,
                ),
            ));
        }
        let x_stride = grid_x.checked_mul(block_x).ok_or_else(|| {
            invalid_driver_value(
                "Function::block_launch",
                "global X thread stride exceeds its u32 wire".into(),
            )
        })?;
        Ok(LinearLaunch {
            grid: Dim3 {
                x: grid_x,
                y: grid_y as u32,
                z: 1,
            },
            block: Dim3::x(block_x),
            x_stride,
        })
    }

    /// Launch this kernel. `params` are pointers to each argument value, in declared order,
    /// exactly as `cuLaunchKernel`'s `kernelParams` expects (e.g. `&mut buf.device_ptr() as *mut _`).
    pub fn launch(&self, grid: Dim3, block: Dim3, params: &mut [*mut c_void]) -> Result<()> {
        self.launch_raw(grid, block, 0, core::ptr::null_mut(), params)
    }

    pub fn launch_on(
        &self,
        stream: &Stream,
        grid: Dim3,
        block: Dim3,
        params: &mut [*mut c_void],
    ) -> Result<()> {
        self.launch_raw(grid, block, 0, stream.stream, params)
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

/// Physical testimony for one stable-address virtual-memory extension.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VirtualDeviceGrowth {
    pub newly_mapped_elements: usize,
    pub mapping_operations: usize,
    pub base_address_unchanged: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct VirtualMapping {
    offset_bytes: usize,
    mapped_bytes: usize,
}

/// One monotonically mapped CUDA virtual-address reservation.
///
/// Logical ordinals retain one flat address space while physical tail pages are added without
/// copying or relocating the prefix. Mapping granularity and the finite reservation are device
/// apparatus. They never become source identities or semantic partitions.
pub struct VirtualDeviceBuffer<T> {
    ptr: ffi::CUdeviceptr,
    logical_reservation_elements: usize,
    reserved_bytes: usize,
    mapped_bytes: usize,
    granularity_bytes: usize,
    device_ordinal: i32,
    mappings: Vec<VirtualMapping>,
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

fn checked_round_up(value: usize, multiple: usize, context: &'static str) -> Result<usize> {
    if multiple == 0 {
        return Err(invalid_driver_value(context, "zero alignment".into()));
    }
    value
        .checked_add(multiple - 1)
        .map(|sum| sum / multiple * multiple)
        .ok_or_else(|| invalid_driver_value(context, "aligned extent overflow".into()))
}

impl<T: DeviceZeroable> VirtualDeviceBuffer<T> {
    pub fn reserve(
        device_ordinal: i32,
        logical_reservation_elements: usize,
        initial_elements: usize,
    ) -> Result<Self> {
        if logical_reservation_elements == 0 || initial_elements > logical_reservation_elements {
            return Err(invalid_driver_value(
                "VirtualDeviceBuffer::reserve",
                "invalid logical reservation".into(),
            ));
        }
        let device = Device::get(device_ordinal)?;
        if device.attribute(DeviceAttribute::VIRTUAL_MEMORY_MANAGEMENT_SUPPORTED)? != 1 {
            return Err(invalid_driver_value(
                "VirtualDeviceBuffer::reserve",
                "device does not support CUDA virtual memory management".into(),
            ));
        }
        let properties = ffi::CUmemAllocationProp {
            allocation_type: 1,
            requested_handle_types: 0,
            location: ffi::CUmemLocation {
                location_type: 1,
                id: device_ordinal,
            },
            ..Default::default()
        };
        let mut granularity_bytes = 0usize;
        unsafe {
            check(
                ffi::cuMemGetAllocationGranularity(&mut granularity_bytes, &properties, 0),
                "cuMemGetAllocationGranularity(MINIMUM)",
            )?
        };
        let logical_bytes = logical_reservation_elements
            .checked_mul(core::mem::size_of::<T>())
            .ok_or_else(|| {
                invalid_driver_value(
                    "VirtualDeviceBuffer::reserve",
                    "byte extent overflow".into(),
                )
            })?;
        let reserved_bytes = checked_round_up(
            logical_bytes,
            granularity_bytes,
            "VirtualDeviceBuffer::reserve",
        )?;
        let mut ptr = 0;
        unsafe {
            check(
                ffi::cuMemAddressReserve(&mut ptr, reserved_bytes, granularity_bytes, 0, 0),
                "cuMemAddressReserve",
            )?
        };
        let mut buffer = Self {
            ptr,
            logical_reservation_elements,
            reserved_bytes,
            mapped_bytes: 0,
            granularity_bytes,
            device_ordinal,
            mappings: Vec::new(),
            _marker: PhantomData,
        };
        if let Err(error) = buffer.ensure_mapped(initial_elements) {
            drop(buffer);
            return Err(error);
        }
        Ok(buffer)
    }

    pub fn ensure_mapped(&mut self, required_elements: usize) -> Result<VirtualDeviceGrowth> {
        if required_elements > self.logical_reservation_elements {
            return Err(invalid_driver_value(
                "VirtualDeviceBuffer::ensure_mapped",
                format!(
                    "required {required_elements} exceeds logical reservation {}",
                    self.logical_reservation_elements
                ),
            ));
        }
        let required_bytes = required_elements
            .checked_mul(core::mem::size_of::<T>())
            .ok_or_else(|| {
                invalid_driver_value(
                    "VirtualDeviceBuffer::ensure_mapped",
                    "byte extent overflow".into(),
                )
            })?;
        let target_bytes = if required_bytes == 0 {
            0
        } else {
            checked_round_up(
                required_bytes,
                self.granularity_bytes,
                "VirtualDeviceBuffer::ensure_mapped",
            )?
        };
        if target_bytes <= self.mapped_bytes {
            return Ok(VirtualDeviceGrowth {
                newly_mapped_elements: 0,
                mapping_operations: 0,
                base_address_unchanged: true,
            });
        }
        let additional_bytes = target_bytes - self.mapped_bytes;
        self.mappings.try_reserve(1).map_err(|error| {
            invalid_driver_value(
                "VirtualDeviceBuffer::ensure_mapped",
                format!("mapping receipt reservation failed: {error}"),
            )
        })?;
        let mut handle = 0;
        let properties = ffi::CUmemAllocationProp {
            allocation_type: 1,
            requested_handle_types: 0,
            location: ffi::CUmemLocation {
                location_type: 1,
                id: self.device_ordinal,
            },
            ..Default::default()
        };
        unsafe {
            check(
                ffi::cuMemCreate(&mut handle, additional_bytes, &properties, 0),
                "cuMemCreate",
            )?
        };
        let address = self
            .ptr
            .checked_add(self.mapped_bytes as u64)
            .ok_or_else(|| {
                invalid_driver_value(
                    "VirtualDeviceBuffer::ensure_mapped",
                    "virtual address overflow".into(),
                )
            })?;
        let map_result = unsafe { ffi::cuMemMap(address, additional_bytes, 0, handle, 0) };
        if let Err(error) = check(map_result, "cuMemMap") {
            unsafe {
                let _ = ffi::cuMemRelease(handle);
            }
            return Err(error);
        }
        let access = ffi::CUmemAccessDesc {
            location: ffi::CUmemLocation {
                location_type: 1,
                id: self.device_ordinal,
            },
            flags: 3,
        };
        let access_result = unsafe { ffi::cuMemSetAccess(address, additional_bytes, &access, 1) };
        if let Err(error) = check(access_result, "cuMemSetAccess(READWRITE)") {
            unsafe {
                let _ = ffi::cuMemUnmap(address, additional_bytes);
                let _ = ffi::cuMemRelease(handle);
            }
            return Err(error);
        }
        let dwords = additional_bytes / core::mem::size_of::<u32>();
        let zero_result = unsafe { cuMemsetD32_v2(address, 0, dwords) };
        if let Err(error) = check(zero_result, "cuMemsetD32_v2(VMM tail)") {
            unsafe {
                let _ = ffi::cuMemUnmap(address, additional_bytes);
                let _ = ffi::cuMemRelease(handle);
            }
            return Err(error);
        }
        if let Err(error) = unsafe { check(ffi::cuMemRelease(handle), "cuMemRelease") } {
            unsafe {
                let _ = ffi::cuMemUnmap(address, additional_bytes);
            }
            return Err(error);
        }
        self.mappings.push(VirtualMapping {
            offset_bytes: self.mapped_bytes,
            mapped_bytes: additional_bytes,
        });
        self.mapped_bytes = target_bytes;
        Ok(VirtualDeviceGrowth {
            newly_mapped_elements: additional_bytes / core::mem::size_of::<T>(),
            mapping_operations: 1,
            base_address_unchanged: true,
        })
    }

    pub fn copy_range_from_slice(&self, offset: usize, src: &[T]) -> Result<()> {
        let end = offset.checked_add(src.len()).ok_or_else(|| {
            invalid_driver_value(
                "VirtualDeviceBuffer::copy_range_from_slice",
                "range overflow".into(),
            )
        })?;
        if end > self.mapped_elements() {
            return Err(invalid_driver_value(
                "VirtualDeviceBuffer::copy_range_from_slice",
                format!(
                    "range {offset}..{end} exceeds mapped extent {}",
                    self.mapped_elements()
                ),
            ));
        }
        if src.is_empty() {
            return Ok(());
        }
        let byte_offset = offset
            .checked_mul(core::mem::size_of::<T>())
            .ok_or_else(|| {
                invalid_driver_value(
                    "VirtualDeviceBuffer::copy_range_from_slice",
                    "byte offset overflow".into(),
                )
            })?;
        let bytes = src
            .len()
            .checked_mul(core::mem::size_of::<T>())
            .ok_or_else(|| {
                invalid_driver_value(
                    "VirtualDeviceBuffer::copy_range_from_slice",
                    "byte length overflow".into(),
                )
            })?;
        let destination = self.ptr.checked_add(byte_offset as u64).ok_or_else(|| {
            invalid_driver_value(
                "VirtualDeviceBuffer::copy_range_from_slice",
                "device address overflow".into(),
            )
        })?;
        unsafe {
            check(
                ffi::cuMemcpyHtoD_v2(destination, src.as_ptr() as *const c_void, bytes),
                "cuMemcpyHtoD_v2(VMM range)",
            )
        }
    }

    pub fn copy_range_to_slice(&self, offset: usize, dst: &mut [T]) -> Result<()> {
        let end = offset.checked_add(dst.len()).ok_or_else(|| {
            invalid_driver_value(
                "VirtualDeviceBuffer::copy_range_to_slice",
                "range overflow".into(),
            )
        })?;
        if end > self.mapped_elements() {
            return Err(invalid_driver_value(
                "VirtualDeviceBuffer::copy_range_to_slice",
                format!(
                    "range {offset}..{end} exceeds mapped extent {}",
                    self.mapped_elements()
                ),
            ));
        }
        if dst.is_empty() {
            return Ok(());
        }
        let byte_offset = offset
            .checked_mul(core::mem::size_of::<T>())
            .ok_or_else(|| {
                invalid_driver_value(
                    "VirtualDeviceBuffer::copy_range_to_slice",
                    "byte offset overflow".into(),
                )
            })?;
        let bytes = dst
            .len()
            .checked_mul(core::mem::size_of::<T>())
            .ok_or_else(|| {
                invalid_driver_value(
                    "VirtualDeviceBuffer::copy_range_to_slice",
                    "byte length overflow".into(),
                )
            })?;
        let source = self.ptr.checked_add(byte_offset as u64).ok_or_else(|| {
            invalid_driver_value(
                "VirtualDeviceBuffer::copy_range_to_slice",
                "device address overflow".into(),
            )
        })?;
        unsafe {
            check(
                ffi::cuMemcpyDtoH_v2(dst.as_mut_ptr() as *mut c_void, source, bytes),
                "cuMemcpyDtoH_v2(VMM range)",
            )
        }
    }

    pub const fn device_ptr(&self) -> ffi::CUdeviceptr {
        self.ptr
    }

    pub const fn base_address(&self) -> ffi::CUdeviceptr {
        self.ptr
    }

    pub const fn logical_reservation_elements(&self) -> usize {
        self.logical_reservation_elements
    }

    pub fn mapped_elements(&self) -> usize {
        self.mapped_bytes / core::mem::size_of::<T>()
    }

    pub const fn mapping_count(&self) -> usize {
        self.mappings.len()
    }

    pub const fn granularity_bytes(&self) -> usize {
        self.granularity_bytes
    }
}

impl<T> Drop for VirtualDeviceBuffer<T> {
    fn drop(&mut self) {
        if self.ptr == 0 {
            return;
        }
        for mapping in self.mappings.iter().rev() {
            unsafe {
                let _ =
                    ffi::cuMemUnmap(self.ptr + mapping.offset_bytes as u64, mapping.mapped_bytes);
            }
        }
        unsafe {
            let _ = ffi::cuMemAddressFree(self.ptr, self.reserved_bytes);
        }
        self.ptr = 0;
    }
}

fn device_dword_count<T: DeviceZeroable>(len: usize) -> usize {
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

    /// Allocate and zero-fill directly on the device. No cpu-sized staging allocation is made.
    pub fn alloc_zeroed(len: usize) -> Result<DeviceBuffer<T>>
    where
        T: DeviceZeroable,
    {
        let buf = DeviceBuffer::alloc(len)?;
        let count = device_dword_count::<T>(len);
        unsafe { check(cuMemsetD32_v2(buf.ptr, 0, count), "cuMemsetD32_v2")? };
        Ok(buf)
    }

    pub fn len(&self) -> usize {
        self.len
    }
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The raw device address, for passing as a kernel argument.
    pub fn device_ptr(&self) -> ffi::CUdeviceptr {
        self.ptr
    }

    pub fn copy_from_slice(&self, src: &[T]) -> Result<()> {
        assert_eq!(src.len(), self.len, "cpu->device length mismatch");
        let bytes = self.len * core::mem::size_of::<T>();
        unsafe {
            check(
                ffi::cuMemcpyHtoD_v2(self.ptr, src.as_ptr() as *const c_void, bytes),
                "cuMemcpyHtoD_v2",
            )
        }
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
            check(
                ffi::cuMemcpyHtoD_v2(destination, src.as_ptr() as *const c_void, bytes),
                "cuMemcpyHtoD_v2(range)",
            )
        }
    }

    pub fn copy_to_slice(&self, dst: &mut [T]) -> Result<()> {
        assert_eq!(dst.len(), self.len, "device->cpu length mismatch");
        let bytes = self.len * core::mem::size_of::<T>();
        unsafe {
            check(
                ffi::cuMemcpyDtoH_v2(dst.as_mut_ptr() as *mut c_void, self.ptr, bytes),
                "cuMemcpyDtoH_v2",
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

    /// Copy one exact typed subspan between allocations in the current context. This is the
    /// resident-lineage remount path: accepted device state need not detour through cpu storage.
    pub fn copy_range_from_buffer(
        &self,
        destination_offset: usize,
        source: &DeviceBuffer<T>,
        source_offset: usize,
        elements: usize,
    ) -> Result<()> {
        let destination_end = destination_offset.checked_add(elements).ok_or_else(|| {
            invalid_driver_value(
                "DeviceBuffer::copy_range_from_buffer",
                "destination range overflow".into(),
            )
        })?;
        let source_end = source_offset.checked_add(elements).ok_or_else(|| {
            invalid_driver_value(
                "DeviceBuffer::copy_range_from_buffer",
                "source range overflow".into(),
            )
        })?;
        if destination_end > self.len || source_end > source.len {
            return Err(invalid_driver_value(
                "DeviceBuffer::copy_range_from_buffer",
                format!(
                    "copy {source_offset}..{source_end} of {} into {destination_offset}..{destination_end} of {}",
                    source.len, self.len
                ),
            ));
        }
        let element_bytes = core::mem::size_of::<T>();
        let destination_bytes = destination_offset
            .checked_mul(element_bytes)
            .ok_or_else(|| {
                invalid_driver_value(
                    "DeviceBuffer::copy_range_from_buffer",
                    "destination byte offset overflow".into(),
                )
            })?;
        let source_bytes = source_offset.checked_mul(element_bytes).ok_or_else(|| {
            invalid_driver_value(
                "DeviceBuffer::copy_range_from_buffer",
                "source byte offset overflow".into(),
            )
        })?;
        let bytes = elements.checked_mul(element_bytes).ok_or_else(|| {
            invalid_driver_value(
                "DeviceBuffer::copy_range_from_buffer",
                "copy byte extent overflow".into(),
            )
        })?;
        let destination = self
            .ptr
            .checked_add(u64::try_from(destination_bytes).map_err(|_| {
                invalid_driver_value(
                    "DeviceBuffer::copy_range_from_buffer",
                    "destination byte offset exceeds the CUDA address wire".into(),
                )
            })?)
            .ok_or_else(|| {
                invalid_driver_value(
                    "DeviceBuffer::copy_range_from_buffer",
                    "destination device address overflow".into(),
                )
            })?;
        let source = source
            .ptr
            .checked_add(u64::try_from(source_bytes).map_err(|_| {
                invalid_driver_value(
                    "DeviceBuffer::copy_range_from_buffer",
                    "source byte offset exceeds the CUDA address wire".into(),
                )
            })?)
            .ok_or_else(|| {
                invalid_driver_value(
                    "DeviceBuffer::copy_range_from_buffer",
                    "source device address overflow".into(),
                )
            })?;
        unsafe {
            check(
                ffi::cuMemcpyDtoD_v2(destination, source, bytes),
                "cuMemcpyDtoD_v2",
            )
        }
    }
}

impl<T: DeviceZeroable> DeviceBuffer<T> {
    /// Return the whole allocation to its canonical zero face directly on the device.
    pub fn zero(&self) -> Result<()> {
        let count = device_dword_count::<T>(self.len);
        unsafe { check(cuMemsetD32_v2(self.ptr, 0, count), "cuMemsetD32_v2") }
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
        assert_eq!(DeviceAttribute::from_raw(123).raw(), 123);
    }

    #[test]
    fn virtual_memory_structures_match_the_cuda_driver_abi() {
        assert_eq!(core::mem::size_of::<ffi::CUmemLocation>(), 8);
        assert_eq!(core::mem::size_of::<ffi::CUmemAllocationFlags>(), 8);
        assert_eq!(core::mem::size_of::<ffi::CUmemAllocationProp>(), 32);
        assert_eq!(core::mem::size_of::<ffi::CUmemAccessDesc>(), 12);
    }

    #[test]
    fn zero_fill_count_is_measured_in_cuda_dwords() {
        assert_eq!(device_dword_count::<u32>(7), 7);
        assert_eq!(device_dword_count::<u64>(7), 14);
    }

    #[test]
    #[ignore = "requires a CUDA device visible to the test process"]
    fn whole_machine_boundary_reads_the_driver_and_zeroes_on_device() -> Result<()> {
        init()?;
        assert!(Device::count()? > 0);
        let device = Device::get(0)?;
        let census = device.launch_census()?;
        assert!(census.max_threads_per_block > 0);
        assert!(census.multiprocessor_count > 0);

        let context = Context::create(&device)?;
        let memory = context.memory_info()?;
        assert!(memory.total_bytes > 0);
        eprintln!(
            "device={} · free={} · total={} bytes · grid={}x{}x{} · threads/block={} · multiprocessors={}",
            device.name,
            memory.free_bytes,
            memory.total_bytes,
            census.max_grid.x,
            census.max_grid.y,
            census.max_grid.z,
            census.max_threads_per_block,
            census.multiprocessor_count,
        );
        let allocation_grain = context.allocation_grain_bytes()?;
        assert!(allocation_grain >= core::mem::size_of::<u32>());
        eprintln!("legacy allocation grain={allocation_grain} bytes");

        let module = Module::load_ptx(crate::SOMA_PTX)?;
        let scope = module.function(soma_abi::register::Entry::ScopeSurface.symbol())?;
        let local = scope.local_size_bytes()?;
        assert!(local > 0);
        eprintln!("scope_register_surface local={local} bytes/thread");

        let buffer: DeviceBuffer<u32> = DeviceBuffer::alloc_zeroed(17)?;
        context.synchronize()?;
        let mut words = [u32::MAX; 17];
        buffer.copy_to_slice(&mut words)?;
        assert_eq!(words, [0; 17]);
        drop(buffer);
        context.destroy()?;
        Ok(())
    }

    #[test]
    #[ignore = "requires a CUDA device with virtual-memory management"]
    fn virtual_device_buffer_maps_a_new_tail_without_readdressing_its_body() -> Result<()> {
        init()?;
        let device = Device::get(0)?;
        let context = Context::create(&device)?;
        let logical_words = 1usize << 24;
        let mut buffer = VirtualDeviceBuffer::<u32>::reserve(0, logical_words, 1)?;
        let base = buffer.base_address();
        let first_mapped = buffer.mapped_elements();
        assert!(first_mapped > 0);
        assert!(first_mapped < logical_words);
        assert_eq!(buffer.mapping_count(), 1);

        buffer.copy_range_from_slice(0, &[11, 13, 17, 19])?;
        let growth = buffer.ensure_mapped(first_mapped + 1)?;
        assert!(growth.newly_mapped_elements > 0);
        assert_eq!(growth.mapping_operations, 1);
        assert!(growth.base_address_unchanged);
        assert_eq!(buffer.base_address(), base);
        assert_eq!(buffer.mapping_count(), 2);

        let mut prefix = [0u32; 4];
        buffer.copy_range_to_slice(0, &mut prefix)?;
        assert_eq!(prefix, [11, 13, 17, 19]);
        let mut new_tail = [u32::MAX; 2];
        buffer.copy_range_to_slice(first_mapped, &mut new_tail)?;
        assert_eq!(new_tail, [0, 0]);
        buffer.copy_range_from_slice(first_mapped, &[23, 29])?;
        buffer.copy_range_to_slice(first_mapped, &mut new_tail)?;
        assert_eq!(new_tail, [23, 29]);

        drop(buffer);
        context.destroy()?;
        Ok(())
    }
}
