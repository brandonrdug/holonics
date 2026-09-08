//! Metal realization of the resident allocation and ordered-command boundary.
//!
//! The legacy `cuda` namespace is retained for source compatibility, not execution.
//! Unsupported CUDA operations return a named obstruction. Native arithmetic is
//! only performed by compiled Metal kernels. Shared buffer bytes are touched by
//! the CPU only at explicit ingress/egress boundaries after GPU completion.

use metal::{MTLCommandBufferStatus, MTLResourceOptions, MTLResourceUsage, MTLSize};
use objc::{msg_send, sel, sel_impl};
use std::{
    cell::{Cell, RefCell},
    collections::BTreeMap,
    ffi::c_void,
    marker::PhantomData,
    mem::size_of,
    rc::{Rc, Weak},
};

#[derive(Debug, Clone)]
pub struct CudaError {
    pub code: i32,
    pub name: String,
    pub message: String,
    pub context: &'static str,
}
impl std::fmt::Display for CudaError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Metal {}: {}: {}", self.context, self.name, self.message)
    }
}
impl std::error::Error for CudaError {}
pub type Result<T> = std::result::Result<T, CudaError>;
fn error(context: &'static str, message: impl Into<String>) -> CudaError {
    CudaError {
        code: 801,
        name: "MetalOperationUnavailable".into(),
        message: message.into(),
        context,
    }
}
fn invalid(context: &'static str, message: impl Into<String>) -> CudaError {
    CudaError {
        code: 1,
        name: "MetalBoundaryError".into(),
        message: message.into(),
        context,
    }
}

struct Runtime {
    device: ::metal::Device,
    queue: ::metal::CommandQueue,
    pending: RefCell<Vec<::metal::CommandBuffer>>,
    failure: RefCell<Option<CudaError>>,
    execution_timing: Cell<MetalExecutionTiming>,
}

/// Cold command-buffer timing supplied by Metal after completion. These floating-point seconds
/// are apparatus measurements only and never participate in native arithmetic or dispatch.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct MetalExecutionTiming {
    pub completed_command_buffers: u64,
    pub unavailable_timestamps: u64,
    pub gpu_seconds: f64,
}
struct Capture {
    runtime: Rc<Runtime>,
    commands: Vec<Command>,
}
thread_local! {
  static CURRENT : RefCell<Option<Rc<Runtime>>> = const {RefCell::new (None)};
  static BUFFERS : RefCell<BTreeMap<u64, Weak<Allocation>>> = const {RefCell::new (BTreeMap::new ())};
  static CAPTURE : RefCell<Option<Capture>> = const {RefCell::new (None)};
}
fn runtime() -> Result<Rc<Runtime>> {
    CURRENT
        .with(|c| c.borrow().clone())
        .ok_or_else(|| invalid("context", "no current Metal context"))
}
#[allow(unexpected_cfgs)] // objc 0.2's selector macro checks the legacy cargo-clippy feature.
fn synchronize(rt: &Runtime) -> Result<()> {
    let pending = std::mem::take(&mut *rt.pending.borrow_mut());
    let mut first_failure = rt.failure.borrow().clone();
    for command in pending {
        command.wait_until_completed();
        let mut timing = rt.execution_timing.get();
        timing.completed_command_buffers += 1;
        // MTLCommandBuffer.h: host seconds at GPU execution start/end; zero means unavailable.
        let command_ref = command.as_ref();
        let start: f64 = unsafe { msg_send![command_ref, GPUStartTime] };
        let end: f64 = unsafe { msg_send![command_ref, GPUEndTime] };
        if start.is_finite() && end.is_finite() && start > 0.0 && end >= start {
            timing.gpu_seconds += end - start;
        } else {
            timing.unavailable_timestamps += 1;
        }
        rt.execution_timing.set(timing);
        if command.status() != MTLCommandBufferStatus::Completed {
            if first_failure.is_none() {
                first_failure = Some(invalid(
                    "synchronize",
                    format!("command status {:?}", command.status()),
                ));
            }
        }
    }
    if let Some(failure) = first_failure {
        *rt.failure.borrow_mut() = Some(failure.clone());
        Err(failure)
    } else {
        Ok(())
    }
}
pub fn init() -> Result<()> {
    if ::metal::Device::system_default().is_none() {
        return Err(error("init", "no Metal device"));
    }
    Ok(())
}
#[derive(Clone)]
pub struct Device {
    pub handle: i32,
    pub name: String,
    inner: ::metal::Device,
}
#[derive(Clone, Copy)]
pub struct DeviceAttribute(i32);
impl DeviceAttribute {
    pub const MAX_THREADS_PER_BLOCK: Self = Self(1);
    pub const MAX_GRID_DIM_X: Self = Self(5);
    pub const MAX_GRID_DIM_Y: Self = Self(6);
    pub const MAX_GRID_DIM_Z: Self = Self(7);
    pub const MULTIPROCESSOR_COUNT: Self = Self(16);
    pub const CONCURRENT_KERNELS: Self = Self(31);
    pub const MAX_BLOCKS_PER_MULTIPROCESSOR: Self = Self(106);
    pub const VIRTUAL_MEMORY_MANAGEMENT_SUPPORTED: Self = Self(102);
    pub const fn from_raw(value: i32) -> Self {
        Self(value)
    }
    pub const fn raw(self) -> i32 {
        self.0
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Dim3 {
    pub x: u32,
    pub y: u32,
    pub z: u32,
}
impl Dim3 {
    pub fn x(x: u32) -> Self {
        Self { x, y: 1, z: 1 }
    }
}
#[derive(Debug, Clone, Copy)]
pub struct LaunchCensus {
    pub max_grid: Dim3,
    pub max_threads_per_block: u32,
    pub multiprocessor_count: u32,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LinearLaunch {
    pub grid: Dim3,
    pub block: Dim3,
    pub x_stride: u32,
}
#[derive(Debug, Clone, Copy)]
pub struct MemoryInfo {
    pub free_bytes: usize,
    pub total_bytes: usize,
}
impl Device {
    pub fn count() -> Result<i32> {
        Ok(i32::from(::metal::Device::system_default().is_some()))
    }
    pub fn get(ordinal: i32) -> Result<Self> {
        if ordinal != 0 {
            return Err(error("device", "only the default Metal device is admitted"));
        }
        let inner =
            ::metal::Device::system_default().ok_or_else(|| error("device", "no Metal device"))?;
        Ok(Self {
            handle: ordinal,
            name: inner.name().into(),
            inner,
        })
    }
    pub fn max_threads(&self) -> u32 {
        self.inner.max_threads_per_threadgroup().width as u32
    }
    pub fn max_shared_bytes(&self) -> u32 {
        self.inner.max_threadgroup_memory_length() as u32
    }
    pub fn unified_memory(&self) -> bool {
        self.inner.has_unified_memory()
    }
    pub fn attribute(&self, attribute: DeviceAttribute) -> Result<i32> {
        match attribute.0 {
            1 => Ok(self.max_threads() as i32),
            8 => Ok(self.max_shared_bytes() as i32),
            41 => Ok(i32::from(self.unified_memory())),
            _ => Err(error(
                "attribute",
                format!(
                    "CUDA attribute {} has no admitted Metal receiver",
                    attribute.0
                ),
            )),
        }
    }
    pub fn launch_census(&self) -> Result<LaunchCensus> {
        Err(error(
            "launch_census",
            "CUDA grid/SM census is not a Metal capability",
        ))
    }
}
pub struct Context {
    inner: Rc<Runtime>,
}
pub struct BorrowedContext {
    inner: Rc<Runtime>,
}
impl Context {
    pub fn create(device: &Device) -> Result<Self> {
        let inner = Rc::new(Runtime {
            device: device.inner.clone(),
            queue: device.inner.new_command_queue(),
            pending: RefCell::new(Vec::new()),
            failure: RefCell::new(None),
            execution_timing: Cell::new(MetalExecutionTiming::default()),
        });
        CURRENT.with(|c| *c.borrow_mut() = Some(inner.clone()));
        Ok(Self { inner })
    }
    pub fn raw(&self) -> *mut c_void {
        Rc::as_ptr(&self.inner) as *mut c_void
    }
    pub fn make_current(&self) -> Result<()> {
        CURRENT.with(|c| *c.borrow_mut() = Some(self.inner.clone()));
        Ok(())
    }
    pub fn synchronize(&self) -> Result<()> {
        synchronize(&self.inner)
    }
    pub fn destroy(self) -> Result<()> {
        self.synchronize()
    }
    pub fn memory_info(&self) -> Result<MemoryInfo> {
        memory_info(&self.inner)
    }
    pub fn allocation_grain_bytes(&self) -> Result<usize> {
        allocation_grain(&self.inner)
    }
    pub fn stack_limit_bytes(&self) -> Result<usize> {
        Err(error(
            "stack_limit",
            "Metal does not expose CUDA stack limits",
        ))
    }
    pub fn ensure_stack_limit_bytes(&self, _: usize) -> Result<usize> {
        self.stack_limit_bytes()
    }
}
impl Drop for Context {
    fn drop(&mut self) {
        CURRENT.with(|c| {
            if c.borrow()
                .as_ref()
                .is_some_and(|current| Rc::ptr_eq(current, &self.inner))
            {
                *c.borrow_mut() = None;
            }
        });
    }
}
impl BorrowedContext {
    /// Observe timestamps already collected at ordinary completion; this does not synchronize.
    pub fn execution_timing(&self) -> MetalExecutionTiming {
        self.inner.execution_timing.get()
    }
    pub fn adopt(raw: *mut c_void) -> Result<Self> {
        let inner = runtime()?;
        if Rc::as_ptr(&inner) as *mut c_void != raw {
            return Err(invalid("adopt", "context is not the current Metal owner"));
        }
        Ok(Self { inner })
    }
    pub fn raw(&self) -> *mut c_void {
        Rc::as_ptr(&self.inner) as *mut c_void
    }
    pub fn make_current(&self) -> Result<()> {
        CURRENT.with(|c| *c.borrow_mut() = Some(self.inner.clone()));
        Ok(())
    }
    pub fn memory_info(&self) -> Result<MemoryInfo> {
        memory_info(&self.inner)
    }
    pub fn allocation_grain_bytes(&self) -> Result<usize> {
        allocation_grain(&self.inner)
    }
}
fn memory_info(rt: &Runtime) -> Result<MemoryInfo> {
    // Metal's recommended working-set budget, not a physical free-VRAM measurement.
    let total = rt.device.recommended_max_working_set_size() as usize;
    let used = rt.device.current_allocated_size() as usize;
    Ok(MemoryInfo {
        free_bytes: total.saturating_sub(used),
        total_bytes: total,
    })
}
fn allocation_grain(rt: &Runtime) -> Result<usize> {
    let probe = rt
        .device
        .new_buffer(1, MTLResourceOptions::StorageModeShared);
    Ok(probe.allocated_size() as usize)
}

struct Allocation {
    buffer: ::metal::Buffer,
    address: u64,
    indirect_address: bool,
    runtime: Rc<Runtime>,
}
impl Drop for Allocation {
    fn drop(&mut self) {
        BUFFERS.with(|b| b.borrow_mut().remove(&self.address));
    }
}
fn resolve(pointer: u64, bytes: usize) -> Result<(Rc<Allocation>, u64)> {
    BUFFERS.with(|buffers| {
        let buffers = buffers.borrow();
        let (&base, weak) = buffers
            .range(..=pointer)
            .next_back()
            .ok_or_else(|| invalid("buffer", "unknown device address"))?;
        let buffer = weak
            .upgrade()
            .ok_or_else(|| invalid("buffer", "released device address"))?;
        let offset = pointer - base;
        if offset
            .checked_add(bytes as u64)
            .is_none_or(|end| end > buffer.buffer.length())
        {
            return Err(invalid(
                "buffer",
                "addressed range exceeds resident allocation",
            ));
        }
        Ok((buffer, offset))
    })
}
pub unsafe trait DeviceZeroable: Copy {}
unsafe impl DeviceZeroable for u32 {}
unsafe impl DeviceZeroable for u64 {}
pub struct DeviceBuffer<T> {
    allocation: Rc<Allocation>,
    len: usize,
    _element: PhantomData<T>,
}
impl<T: Copy> DeviceBuffer<T> {
    #[allow(unexpected_cfgs)] // objc 0.2 selector macros check their legacy cargo-clippy feature.
    pub fn alloc(len: usize) -> Result<Self> {
        let bytes = len
            .checked_mul(size_of::<T>())
            .filter(|b| *b > 0)
            .ok_or_else(|| invalid("alloc", "invalid extent"))?;
        let rt = runtime()?;
        if bytes as u64 > rt.device.max_buffer_length() {
            return Err(error("alloc", "Metal maximum buffer extent exceeded"));
        }
        let buffer = rt
            .device
            .new_buffer(bytes as u64, MTLResourceOptions::StorageModeShared);
        // Direct bindings retain support for older Metal hosts. An indirect factor query below
        // requires an actual GPU virtual address and explicitly refuses the fallback address.
        let indirect_address: bool =
            unsafe { msg_send![buffer.as_ref(), respondsToSelector: sel!(gpuAddress)] };
        let address = if indirect_address {
            buffer.gpu_address()
        } else {
            buffer.contents() as u64
        };
        let allocation = Rc::new(Allocation {
            buffer,
            address,
            indirect_address,
            runtime: rt,
        });
        BUFFERS.with(|b| {
            b.borrow_mut()
                .insert(allocation.address, Rc::downgrade(&allocation))
        });
        Ok(Self {
            allocation,
            len,
            _element: PhantomData,
        })
    }
    pub fn len(&self) -> usize {
        self.len
    }
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
    pub fn device_ptr(&self) -> u64 {
        self.allocation.address
    }
    pub fn copy_from_slice(&self, src: &[T]) -> Result<()> {
        if src.len() != self.len {
            return Err(invalid("copy_from_slice", "extent mismatch"));
        }
        self.copy_range_from_slice(0, src)
    }
    pub fn copy_to_slice(&self, dst: &mut [T]) -> Result<()> {
        if dst.len() != self.len {
            return Err(invalid("copy_to_slice", "extent mismatch"));
        }
        self.copy_range_to_slice(0, dst)
    }
    pub fn copy_range_from_slice(&self, offset: usize, src: &[T]) -> Result<()> {
        self.range(offset, src.len())?;
        synchronize(&self.allocation.runtime)?;
        unsafe {
            std::ptr::copy_nonoverlapping(
                src.as_ptr(),
                self.allocation.buffer.contents().cast::<T>().add(offset),
                src.len(),
            );
        }
        Ok(())
    }
    pub fn copy_range_to_slice(&self, offset: usize, dst: &mut [T]) -> Result<()> {
        self.range(offset, dst.len())?;
        synchronize(&self.allocation.runtime)?;
        unsafe {
            std::ptr::copy_nonoverlapping(
                self.allocation.buffer.contents().cast::<T>().add(offset),
                dst.as_mut_ptr(),
                dst.len(),
            );
        }
        Ok(())
    }
    fn range(&self, offset: usize, len: usize) -> Result<()> {
        if offset.checked_add(len).is_none_or(|end| end > self.len) {
            return Err(invalid("copy", "extent exceeds buffer"));
        }
        Ok(())
    }
    pub fn copy_range_from_buffer(
        &self,
        dst_offset: usize,
        source: &Self,
        src_offset: usize,
        count: usize,
    ) -> Result<()> {
        self.range(dst_offset, count)?;
        source.range(src_offset, count)?;
        if !Rc::ptr_eq(&self.allocation.runtime, &source.allocation.runtime) {
            return Err(invalid(
                "copy",
                "source and destination belong to different contexts",
            ));
        }
        if Rc::ptr_eq(&self.allocation, &source.allocation) {
            let dst_end = dst_offset
                .checked_add(count)
                .ok_or_else(|| invalid("copy", "destination extent overflow"))?;
            let src_end = src_offset
                .checked_add(count)
                .ok_or_else(|| invalid("copy", "source extent overflow"))?;
            if dst_offset < src_end && src_offset < dst_end {
                return Err(invalid("copy", "overlapping resident copy is unsupported"));
            }
        }
        let stream = Stream::create()?;
        stream.copy_device_to_device_async(
            self.device_ptr() + (dst_offset * size_of::<T>()) as u64,
            source.device_ptr() + (src_offset * size_of::<T>()) as u64,
            count * size_of::<T>(),
        )?;
        stream.synchronize()
    }
    pub fn alloc_zeroed(len: usize) -> Result<Self>
    where
        T: DeviceZeroable,
    {
        let b = Self::alloc(len)?;
        b.zero()?;
        Ok(b)
    }
}
impl<T: DeviceZeroable> DeviceBuffer<T> {
    pub fn zero(&self) -> Result<()> {
        let stream = Stream::create()?;
        stream.memset_u32_async(self.device_ptr(), 0, self.len * size_of::<T>() / 4)?;
        stream.synchronize()
    }
}

#[derive(Clone)]
enum Argument {
    Buffer(Rc<Allocation>, u64),
    NullBuffer,
    U32(u32),
    U32Array(Vec<u32>),
    U64Array(Vec<u64>),
    U64(u64),
}
#[derive(Clone)]
enum Command {
    Kernel {
        pipeline: ::metal::ComputePipelineState,
        arguments: Vec<Argument>,
        indirect: Vec<Rc<Allocation>>,
        scratch: u64,
        grid: MTLSize,
        block: MTLSize,
    },
    Fill {
        buffer: Rc<Allocation>,
        offset: u64,
        bytes: u64,
    },
    Copy {
        src: Rc<Allocation>,
        src_offset: u64,
        dst: Rc<Allocation>,
        dst_offset: u64,
        bytes: u64,
    },
}
fn submit(rt: &Runtime, commands: &[Command]) -> Result<()> {
    // Encoders and command buffers are autoreleased Objective-C objects. Keep the owned
    // command-buffer reference until completion, but release temporary encoder references
    // after encoding even in command-line applications without an ambient Cocoa run loop.
    objc::rc::autoreleasepool(|| submit_in_pool(rt, commands))
}
fn submit_in_pool(rt: &Runtime, commands: &[Command]) -> Result<()> {
    if let Some(failure) = rt.failure.borrow().clone() {
        return Err(failure);
    }
    let cb = rt.queue.new_command_buffer().to_owned();
    for command in commands {
        match command {
            Command::Kernel {
                pipeline,
                arguments,
                indirect,
                scratch,
                grid,
                block,
            } => {
                let enc = cb.new_compute_command_encoder();
                enc.set_compute_pipeline_state(pipeline);
                for (i, arg) in arguments.iter().enumerate() {
                    match arg {
                        Argument::Buffer(b, offset) => {
                            enc.set_buffer(i as u64, Some(&b.buffer), *offset)
                        }
                        Argument::NullBuffer => enc.set_buffer(i as u64, None, 0),
                        Argument::U32(v) => enc.set_bytes(i as u64, 4, (v as *const u32).cast()),
                        Argument::U64(v) => enc.set_bytes(i as u64, 8, (v as *const u64).cast()),
                        Argument::U32Array(values) => enc.set_bytes(
                            i as u64,
                            (values.len() * size_of::<u32>()) as u64,
                            values.as_ptr().cast(),
                        ),
                        Argument::U64Array(values) => enc.set_bytes(
                            i as u64,
                            (values.len() * size_of::<u64>()) as u64,
                            values.as_ptr().cast(),
                        ),
                    }
                }
                for buffer in indirect {
                    enc.use_resource(&buffer.buffer, MTLResourceUsage::Read);
                }
                if *scratch > 0 {
                    enc.set_threadgroup_memory_length(0, *scratch);
                }
                enc.dispatch_thread_groups(*grid, *block);
                enc.end_encoding();
            }
            Command::Fill {
                buffer,
                offset,
                bytes,
            } => {
                let enc = cb.new_blit_command_encoder();
                enc.fill_buffer(&buffer.buffer, ::metal::NSRange::new(*offset, *bytes), 0);
                enc.end_encoding();
            }
            Command::Copy {
                src,
                src_offset,
                dst,
                dst_offset,
                bytes,
            } => {
                let enc = cb.new_blit_command_encoder();
                enc.copy_from_buffer(&src.buffer, *src_offset, &dst.buffer, *dst_offset, *bytes);
                enc.end_encoding();
            }
        }
    }
    cb.commit();
    rt.pending.borrow_mut().push(cb);
    Ok(())
}
fn record(rt: &Rc<Runtime>, command: Command) -> Result<()> {
    let mut command = Some(command);
    let mut capture_error = None;
    CAPTURE.with(|capture| {
        let mut capture = capture.borrow_mut();
        if let Some(active) = capture.as_mut() {
            if !Rc::ptr_eq(&active.runtime, rt) {
                capture_error = Some(invalid("capture", "command belongs to another context"));
            } else {
                active.commands.push(command.take().unwrap());
            }
        }
    });
    if let Some(error) = capture_error {
        return Err(error);
    }
    if let Some(command) = command {
        submit(rt, &[command])?;
    }
    Ok(())
}
pub struct Stream {
    runtime: Rc<Runtime>,
    capture_owner: Cell<bool>,
}
impl Stream {
    pub fn create() -> Result<Self> {
        Ok(Self {
            runtime: runtime()?,
            capture_owner: Cell::new(false),
        })
    }
    pub fn synchronize(&self) -> Result<()> {
        synchronize(&self.runtime)
    }
    pub const fn is_nonblocking(&self) -> bool {
        true
    }
    pub fn raw(&self) -> *mut c_void {
        Rc::as_ptr(&self.runtime) as *mut c_void
    }
    pub fn begin_capture(&self) -> Result<()> {
        CAPTURE.with(|c| {
            let mut c = c.borrow_mut();
            if c.is_some() {
                return Err(invalid("capture", "nested capture"));
            }
            *c = Some(Capture {
                runtime: self.runtime.clone(),
                commands: Vec::new(),
            });
            self.capture_owner.set(true);
            Ok(())
        })
    }
    pub fn end_capture(&self) -> Result<Graph> {
        if !self.capture_owner.replace(false) {
            return Err(invalid("capture", "this stream does not own capture"));
        }
        CAPTURE
            .with(|c| c.borrow_mut().take())
            .map(|capture| {
                if !Rc::ptr_eq(&capture.runtime, &self.runtime) {
                    return Err(invalid("capture", "capture belongs to another context"));
                }
                Ok(Graph {
                    runtime: capture.runtime,
                    commands: capture.commands,
                })
            })
            .transpose()?
            .ok_or_else(|| invalid("capture", "no active capture"))
    }
    pub fn wait_event(&self, event: &Event) -> Result<()> {
        if !Rc::ptr_eq(&self.runtime, &event.runtime) {
            return Err(invalid("event", "foreign context"));
        }
        if !*event.recorded.borrow() {
            return Err(invalid("event", "event has not been recorded"));
        }
        // One Metal queue preserves the full topological order. No parallelism claim.
        Ok(())
    }
    pub fn memset_u32_async(&self, pointer: u64, value: u32, count: usize) -> Result<()> {
        if value != 0 {
            return Err(error("memset", "only zero initialization is implemented"));
        }
        let bytes = count
            .checked_mul(4)
            .ok_or_else(|| invalid("memset", "extent overflow"))?;
        let (buffer, offset) = resolve(pointer, bytes)?;
        if !Rc::ptr_eq(&buffer.runtime, &self.runtime) {
            return Err(invalid("memset", "buffer belongs to another context"));
        }
        record(
            &self.runtime,
            Command::Fill {
                buffer,
                offset,
                bytes: bytes as u64,
            },
        )
    }
    pub fn copy_device_to_device_async(
        &self,
        destination: u64,
        source: u64,
        bytes: usize,
    ) -> Result<()> {
        let (src, src_offset) = resolve(source, bytes)?;
        let (dst, dst_offset) = resolve(destination, bytes)?;
        if !Rc::ptr_eq(&src.runtime, &self.runtime) || !Rc::ptr_eq(&dst.runtime, &self.runtime) {
            return Err(invalid("copy", "buffer belongs to another context"));
        }
        record(
            &self.runtime,
            Command::Copy {
                src,
                src_offset,
                dst,
                dst_offset,
                bytes: bytes as u64,
            },
        )
    }
    pub unsafe fn copy_host_to_device_async(
        &self,
        _: u64,
        _: *const c_void,
        _: usize,
    ) -> Result<()> {
        Err(error(
            "async ingress",
            "use owned staging; borrowed host memory is not retained by a Metal command",
        ))
    }
}
impl Drop for Stream {
    fn drop(&mut self) {
        if self.capture_owner.get() {
            CAPTURE.with(|c| {
                if c.borrow()
                    .as_ref()
                    .is_some_and(|capture| Rc::ptr_eq(&capture.runtime, &self.runtime))
                {
                    c.borrow_mut().take();
                }
            });
        }
    }
}
pub struct Event {
    runtime: Rc<Runtime>,
    recorded: RefCell<bool>,
}
impl Event {
    pub fn create() -> Result<Self> {
        Ok(Self {
            runtime: runtime()?,
            recorded: RefCell::new(false),
        })
    }
    pub fn record(&self, stream: &Stream) -> Result<()> {
        if !Rc::ptr_eq(&self.runtime, &stream.runtime) {
            return Err(invalid("event", "foreign context"));
        }
        *self.recorded.borrow_mut() = true;
        Ok(())
    }
    pub fn synchronize(&self) -> Result<()> {
        synchronize(&self.runtime)
    }
}
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct GraphCensus {
    pub nodes: usize,
    pub edges: usize,
    pub kernel_nodes: usize,
    pub memset_nodes: usize,
    pub memcpy_nodes: usize,
    pub other_nodes: usize,
}
pub struct Graph {
    runtime: Rc<Runtime>,
    commands: Vec<Command>,
}
pub struct GraphExec {
    runtime: Rc<Runtime>,
    commands: Vec<Command>,
}
impl Graph {
    pub fn census(&self) -> Result<GraphCensus> {
        let mut c = GraphCensus {
            nodes: self.commands.len(),
            edges: self.commands.len().saturating_sub(1),
            ..Default::default()
        };
        for command in &self.commands {
            match command {
                Command::Kernel { .. } => c.kernel_nodes += 1,
                Command::Fill { .. } => c.memset_nodes += 1,
                Command::Copy { .. } => c.memcpy_nodes += 1,
            }
        }
        Ok(c)
    }
    pub fn instantiate(&self) -> Result<GraphExec> {
        Ok(GraphExec {
            runtime: self.runtime.clone(),
            commands: self.commands.clone(),
        })
    }
}
impl GraphExec {
    pub fn launch(&self, stream: &Stream) -> Result<()> {
        if !Rc::ptr_eq(&self.runtime, &stream.runtime) {
            return Err(invalid("graph launch", "graph belongs to another context"));
        }
        submit(&stream.runtime, &self.commands)
    }
}

pub struct Module {
    // Immutable compiled apparatus is shared; current/state buffers are never cached here.
    pipelines: RefCell<BTreeMap<String, ::metal::ComputePipelineState>>,
    library: ::metal::Library,
    runtime: Rc<Runtime>,
}
pub struct Function<'m> {
    pipeline: ::metal::ComputePipelineState,
    signature: &'static [usize],
    wide_signature: &'static [usize],
    arity: usize,
    pack_scalars: bool,
    pack_wide_scalars: bool,
    indirect_table: Option<(usize, usize, usize)>,
    parallel_grid: bool,
    nullable: &'static [usize],
    runtime: Rc<Runtime>,
    _module: PhantomData<&'m Module>,
}
impl Module {
    pub fn load_ptx(_: &[u8]) -> Result<Self> {
        Err(error("load_ptx", "CUDA PTX is unavailable on Metal"))
    }
    pub fn load_metal(source: &str) -> Result<Self> {
        objc::rc::autoreleasepool(|| {
            let runtime = runtime()?;
            let options = ::metal::CompileOptions::new();
            options.set_fast_math_enabled(false);
            let library = runtime
                .device
                .new_library_with_source(source, &options)
                .map_err(|e| invalid("compile", e))?;
            Ok(Self {
                library,
                runtime,
                pipelines: RefCell::new(BTreeMap::new()),
            })
        })
    }
    pub fn function(&self, name: &str) -> Result<Function<'_>> {
        // Scalar positions and arity are the exact published kernel ABI, not semantic routing.
        let (signature, arity): (&'static [usize], usize) = match name {
            #[cfg(test)]
            "test_grid" => (&[1], 2),
            #[cfg(test)]
            "test_indirect" => (&[1], 3),
            "conduct_complex_incidence" => (&[5, 6, 7], 8),
            "section_constitutive_fibre" => (&[4, 5, 6, 12], 13),
            "section_constitutive_current" => (&[4, 5, 6, 9, 10, 11, 12, 13, 14, 20], 21),
            "section_constitutive_bilinear_source" => (&[2, 3, 4, 7, 8, 9, 10, 11, 17], 18),
            "section_phase_convolution" => (&[2, 3, 4, 7, 8, 9, 10, 11, 12, 13, 19], 20),
            "section_constitutive_differential" => (&[2, 3, 4, 5, 13], 14),
            "section_constitutive_condition_preimage" => (&[3, 4, 5, 8, 9, 10, 11, 12, 13, 23], 24),
            "section_constitutive_condition_image" => (&[3, 4, 5, 8, 9, 10, 11, 33], 34),
            "section_constitutive_condition_receive" => (&[2, 3, 4, 9, 10, 11, 21], 22),
            "section_constitutive_condition_current_found" => (&[2, 3, 4, 5, 11], 12),
            "section_constitutive_condition_contact" => (&[2, 3, 4, 7, 8, 16], 17),
            "section_phase_convolution_validate" | "section_phase_convolution_products" => {
                (&[2, 3, 4, 7, 8, 9, 10, 11, 12, 13, 18], 19)
            }
            "section_phase_difference_validate" | "section_phase_difference_products" => {
                (&[2, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 21], 22)
            }
            "section_phase_convolution_normalize" => (&[1, 5], 6),
            "section_phase_response_adjoint_validate"
            | "section_phase_response_adjoint_products" => {
                (&[2, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15, 20], 21)
            }
            "section_phase_convolution_pack" => (&[1, 7], 8),
            "section_phase_enclosure_lift" => (&[2, 3, 4, 5, 6, 7, 13], 14),
            "section_phase_enclosed_convolution_validate" => (&[2, 3, 4, 7, 8, 9, 10, 11, 16], 17),
            "section_phase_enclosed_convolution_lift" => (&[1, 2, 3, 4, 5, 10], 11),
            "section_phase_enclosed_convolution_products" => (&[1, 2, 3, 4, 11], 12),
            "section_phase_enclosed_convolution_finish" => (&[1, 2, 3, 9], 10),
            "section_phase_enclosed_difference_validate" => {
                (&[2, 3, 6, 7, 8, 9, 10, 11, 12, 13, 14, 19], 20)
            }
            "section_phase_enclosed_difference_products" => (&[1, 3, 4, 5, 6, 7, 14], 15),
            "section_phase_enclosed_difference_finish" => (&[1, 7], 8),
            "section_temporal_condition_contact_validate"
            | "section_temporal_condition_contact_gram"
            | "section_temporal_condition_contact_rhs"
            | "section_temporal_condition_contact_solve" => (
                &[
                    2, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 20, 21, 28, 29,
                ],
                30,
            ),
            "section_field_current_input" => (&[2, 3, 4, 5, 11], 12),
            "section_field_source_frame" => (&[6, 12], 13),
            "section_field_internal_current" => (&[9, 10, 11, 12, 20], 21),
            "section_internal_shared_drive" => (&[4, 8], 9),
            "section_internal_mode_unfold" => (&[2, 8], 9),
            "section_field_current_history_source" => (&[10, 11, 12, 21], 22),
            "section_field_current_history_pairing" => (&[4, 10], 11),
            "section_complete_material_source_current" => (&[2, 3, 9], 10),
            "section_complete_material_source_reading" => (&[3, 4, 10], 11),
            "section_complete_material_mode" => (&[9, 10, 11, 22], 23),
            "section_material_mode_unfold" => (&[1, 8], 9),
            "section_field_differential_receiver" => (&[2, 3, 4, 5, 11], 12),
            "section_constitutive_circulation" => (&[9, 10, 16], 17),
            "section_constitutive_rechart" => (&[5, 19], 20),
            "section_constitutive_field" => (&[9, 10, 11, 12, 21, 36], 37),
            "section_constitutive_field_rechart" => (&[5, 19], 20),
            "section_census" | "section_census_serial_control" => (&[2, 3], 5),
            "section_carry" => (&[2, 8], 9),
            _ => {
                return Err(error(
                    "function",
                    format!("native operation {name} has not been realized on Metal"),
                ));
            }
        };
        objc::rc::autoreleasepool(|| {
            let cached = self.pipelines.borrow().get(name).cloned();
            let pipeline = if let Some(pipeline) = cached {
                pipeline
            } else {
                let function = self
                    .library
                    .get_function(name, None)
                    .map_err(|e| invalid("function", e))?;
                let pipeline = self
                    .runtime
                    .device
                    .new_compute_pipeline_state_with_function(&function)
                    .map_err(|e| invalid("pipeline", e))?;
                self.pipelines
                    .borrow_mut()
                    .insert(name.to_owned(), pipeline.clone());
                pipeline
            };
            Ok(Function {
                pipeline,
                signature,
                wide_signature: if name == "section_constitutive_field" {
                    &[13]
                } else if name == "section_field_internal_current" {
                    &[12]
                } else if name == "section_internal_mode_unfold"
                    || name == "section_material_mode_unfold"
                {
                    &[2]
                } else if name == "section_field_current_history_source" {
                    &[13]
                } else if name == "section_complete_material_mode" {
                    &[12, 13, 14, 15, 16]
                } else {
                    &[]
                },
                arity,
                pack_scalars: name == "section_constitutive_condition_image",
                pack_wide_scalars: name == "section_constitutive_field",
                indirect_table: match name {
                    "section_complete_material_source_current" => Some((1, 2, 2)),
                    "section_complete_material_mode" => Some((8, 9, 4)),
                    #[cfg(test)]
                    "test_indirect" => Some((0, 1, 2)),
                    _ => None,
                },
                parallel_grid: matches!(
                    name,
                    "section_phase_convolution_products"
                        | "section_phase_convolution_pack"
                        | "section_phase_difference_products"
                        | "section_phase_response_adjoint_products"
                        | "section_phase_enclosed_convolution_lift"
                        | "section_phase_enclosed_convolution_products"
                        | "section_phase_enclosed_difference_products"
                        | "section_temporal_condition_contact_gram"
                        | "section_temporal_condition_contact_rhs"
                ) || (cfg!(test) && name == "test_grid"),
                nullable: if name == "section_constitutive_differential" {
                    &[6, 7]
                } else if name == "section_constitutive_field" {
                    &[
                        14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 28, 29, 30,
                    ]
                } else if name == "section_complete_material_source_reading" {
                    &[2]
                } else if name == "section_complete_material_mode" {
                    &[2, 3]
                } else {
                    &[]
                },
                runtime: self.runtime.clone(),
                _module: PhantomData,
            })
        })
    }
}
impl Function<'_> {
    pub fn max_threads_per_block(&self) -> Result<u32> {
        Ok(self.pipeline.max_total_threads_per_threadgroup() as u32)
    }
    pub fn execution_width(&self) -> u32 {
        self.pipeline.thread_execution_width() as u32
    }
    pub fn static_shared_bytes(&self) -> Result<u32> {
        Ok(self.pipeline.static_threadgroup_memory_length() as u32)
    }
    pub fn num_regs(&self) -> Result<u32> {
        Err(error("register census", "not exposed by Metal"))
    }
    pub fn local_size_bytes(&self) -> Result<usize> {
        Err(error("local memory census", "not exposed by Metal"))
    }
    pub fn linear_launch(&self, _: LaunchCensus, _: u64) -> Result<LinearLaunch> {
        Err(error(
            "linear_launch",
            "use the native Metal operation descriptor",
        ))
    }
    pub fn block_launch(&self, _: LaunchCensus, _: u64, _: u32) -> Result<LinearLaunch> {
        Err(error(
            "block_launch",
            "use the native Metal operation descriptor",
        ))
    }
    pub fn launch(&self, grid: Dim3, block: Dim3, params: &mut [*mut c_void]) -> Result<()> {
        self.launch_on_shared(&Stream::create()?, grid, block, 0, params)
    }
    pub fn launch_on(
        &self,
        stream: &Stream,
        grid: Dim3,
        block: Dim3,
        params: &mut [*mut c_void],
    ) -> Result<()> {
        self.launch_on_shared(stream, grid, block, 0, params)
    }
    pub fn launch_on_shared(
        &self,
        stream: &Stream,
        grid: Dim3,
        block: Dim3,
        shared: u32,
        params: &mut [*mut c_void],
    ) -> Result<()> {
        if !Rc::ptr_eq(&self.runtime, &stream.runtime) || params.len() != self.arity {
            return Err(invalid("launch", "context or kernel argument mismatch"));
        }
        // Only explicitly independent coordinate kernels admit a flat parallel grid. Existing
        // complete serial kernels loop over their declared carriers and retain one thread.
        let (grid, block) = if self.parallel_grid {
            if grid.x == 0
                || block.x == 0
                || grid.y != 1
                || grid.z != 1
                || block.y != 1
                || block.z != 1
                || block.x as u64 > self.pipeline.max_total_threads_per_threadgroup()
                || grid.x as u64 * block.x as u64 > u32::MAX as u64 + 1
            {
                return Err(invalid(
                    "launch",
                    "parallel kernel requires an admitted flat u32 grid",
                ));
            }
            (
                MTLSize::new(grid.x as u64, 1, 1),
                MTLSize::new(block.x as u64, 1, 1),
            )
        } else {
            (MTLSize::new(1, 1, 1), MTLSize::new(1, 1, 1))
        };
        let scratch = shared
            .checked_add(15)
            .ok_or_else(|| invalid("launch", "threadgroup scratch extent overflow"))?
            & !15;
        if scratch as u64 + self.pipeline.static_threadgroup_memory_length()
            > self.runtime.device.max_threadgroup_memory_length()
        {
            return Err(error(
                "launch",
                "threadgroup scratch exceeds device aperture",
            ));
        }
        let mut arguments = Vec::with_capacity(params.len());
        let mut wide_scalars = Vec::new();
        let mut scalars = if self.pack_scalars {
            Vec::with_capacity(self.signature.len())
        } else {
            Vec::new()
        };
        for (index, pointer) in params.iter().enumerate() {
            if pointer.is_null() {
                return Err(invalid("launch", "null argument storage"));
            }
            if self.wide_signature.contains(&index) {
                let value = unsafe { *(*pointer as *const u64) };
                if self.pack_wide_scalars {
                    wide_scalars.push(value);
                } else {
                    arguments.push(Argument::U64(value));
                }
            } else if self.signature.contains(&index) {
                let value = unsafe { *(*pointer as *const u32) };
                if self.pack_scalars {
                    scalars.push(value);
                } else if self.pack_wide_scalars {
                    wide_scalars.push(u64::from(value));
                } else {
                    arguments.push(Argument::U32(value));
                }
            } else {
                let address = unsafe { *(*pointer as *const u64) };
                if address == 0 && self.nullable.contains(&index) {
                    arguments.push(Argument::NullBuffer);
                    continue;
                }
                let (buffer, offset) = resolve(address, 1)?;
                if !Rc::ptr_eq(&buffer.runtime, &self.runtime) {
                    return Err(invalid("launch", "buffer belongs to another context"));
                }
                arguments.push(Argument::Buffer(buffer, offset));
            }
        }
        // The shared image ABI has 34 arguments, beyond Metal's 31 buffer slots. Its eight
        // immutable u32 launch fields share the final constant buffer; 26 current/evidence
        // pointers remain in their original order. No numerical current crosses this boundary.
        if self.pack_scalars {
            arguments.push(Argument::U32Array(scalars));
        } else if self.pack_wide_scalars {
            arguments.push(Argument::U64Array(wide_scalars));
        }
        // These two native ABIs receive immutable exterior address tables. Inspect only their
        // pointer columns, never numerical factor/source carriers. Keep the addressed buffers
        // alive with this command and declare their indirect read residency to Metal.
        let mut indirect = Vec::new();
        if let Some((table_index, count_index, stride)) = self.indirect_table {
            let address = unsafe { *(params[table_index] as *const u64) };
            let count = unsafe { *(params[count_index] as *const u32) } as usize;
            let bytes = count
                .checked_mul(stride)
                .and_then(|n| n.checked_mul(8))
                .ok_or_else(|| invalid("indirect table", "address table extent overflow"))?;
            let (table, offset) = resolve(address, bytes)?;
            if offset % 8 != 0
                || self.runtime.device.argument_buffers_support()
                    != ::metal::MTLArgumentBuffersTier::Tier2
            {
                return Err(error(
                    "indirect table",
                    "aligned tier-2 GPU address table required",
                ));
            }
            let words = unsafe {
                std::slice::from_raw_parts(
                    table
                        .buffer
                        .contents()
                        .cast::<u64>()
                        .add(offset as usize / 8),
                    count * stride,
                )
            };
            for row in words.chunks_exact(stride) {
                for (column, &pointer) in row[..2].iter().enumerate() {
                    if pointer == 0 && stride == 4 && column == 1 {
                        continue;
                    }
                    let (buffer, offset) = resolve(pointer, 8)?;
                    if offset % 8 != 0
                        || !buffer.indirect_address
                        || !Rc::ptr_eq(&buffer.runtime, &self.runtime)
                    {
                        return Err(invalid(
                            "indirect table",
                            "foreign or unavailable GPU address",
                        ));
                    }
                    indirect.push(buffer);
                }
            }
        }
        record(
            &self.runtime,
            Command::Kernel {
                pipeline: self.pipeline.clone(),
                arguments,
                indirect,
                scratch: scratch as u64,
                grid,
                block,
            },
        )
    }
}

pub struct PinnedHost {
    bytes: Vec<u8>,
}
impl PinnedHost {
    pub fn alloc(_: usize) -> Result<Self> {
        Err(error(
            "pinned host",
            "CUDA pinned-host asynchronous ingress is not implemented on Metal",
        ))
    }
    pub fn octets(&self) -> usize {
        self.bytes.len()
    }
    pub fn as_ptr(&self) -> *const c_void {
        self.bytes.as_ptr().cast()
    }
    pub fn as_mut_octets(&mut self) -> &mut [u8] {
        &mut self.bytes
    }
    pub unsafe fn as_octets_unchecked(&self) -> &mut [u8] {
        panic!("unowned asynchronous host mutation is unsupported on Metal")
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VirtualDeviceGrowth {
    pub newly_mapped_elements: usize,
    pub mapping_operations: usize,
    pub base_address_unchanged: bool,
}
pub struct VirtualDeviceBuffer<T> {
    _element: PhantomData<T>,
}
impl<T: DeviceZeroable> VirtualDeviceBuffer<T> {
    pub fn reserve(_: i32, _: usize, _: usize) -> Result<Self> {
        Err(error(
            "virtual memory",
            "CUDA virtual reservations have not been realized on Metal",
        ))
    }
    pub fn ensure_mapped(&mut self, _: usize) -> Result<VirtualDeviceGrowth> {
        Err(error("virtual memory", "unavailable"))
    }
    pub fn copy_range_from_slice(&self, _: usize, _: &[T]) -> Result<()> {
        Err(error("virtual memory", "unavailable"))
    }
    pub fn copy_range_to_slice(&self, _: usize, _: &mut [T]) -> Result<()> {
        Err(error("virtual memory", "unavailable"))
    }
    pub fn device_ptr(&self) -> u64 {
        unreachable!("virtual Metal buffers cannot be constructed")
    }
    pub fn base_address(&self) -> u64 {
        self.device_ptr()
    }
    pub fn logical_reservation_elements(&self) -> usize {
        unreachable!()
    }
    pub fn mapped_elements(&self) -> usize {
        unreachable!()
    }
    pub fn mapping_count(&self) -> usize {
        unreachable!()
    }
    pub fn granularity_bytes(&self) -> usize {
        unreachable!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{Mutex, OnceLock};

    fn guard() -> std::sync::MutexGuard<'static, ()> {
        static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
        LOCK.get_or_init(|| Mutex::new(())).lock().unwrap()
    }

    fn context() -> (std::sync::MutexGuard<'static, ()>, Context) {
        let lock = guard();
        let device = Device::get(0).expect("Metal device required for mount tests");
        (lock, Context::create(&device).expect("Metal context"))
    }

    #[test]
    fn shared_buffer_roundtrip_is_exact() {
        let (_lock, context) = context();
        let buffer = DeviceBuffer::<u32>::alloc(4).unwrap();
        let input = [0x1122_3344, 0x5566_7788, 0, u32::MAX];
        buffer.copy_from_slice(&input).unwrap();
        let mut output = [0u32; 4];
        buffer.copy_to_slice(&mut output).unwrap();
        assert_eq!(output, input);
        context.synchronize().unwrap();
    }

    #[test]
    fn captured_indirect_factors_keep_their_allocations_and_offsets() {
        let (_lock, context) = context();
        let module = Module::load_metal(
            r#"
            #include <metal_stdlib>
            using namespace metal;
            struct Factor { device const long *left; device const long *right; };
            kernel void test_indirect(device const Factor *factors [[buffer(0)]],
                constant uint &count [[buffer(1)]], device long *output [[buffer(2)]]) {
                long sum = 0;
                for (uint i=0; i<count; ++i) sum += *factors[i].left + *factors[i].right;
                *output = sum;
            }
        "#,
        )
        .unwrap();
        let function = module.function("test_indirect").unwrap();
        let left = DeviceBuffer::<i64>::alloc(3).unwrap();
        left.copy_from_slice(&[3, 5, 7]).unwrap();
        let right = DeviceBuffer::<i64>::alloc(2).unwrap();
        right.copy_from_slice(&[11, 13]).unwrap();
        let left_address = left.device_ptr();
        let factors = DeviceBuffer::<u64>::alloc(4).unwrap();
        factors
            .copy_from_slice(&[
                left_address + 8,
                right.device_ptr(),
                left_address + 16,
                right.device_ptr() + 8,
            ])
            .unwrap();
        let output = DeviceBuffer::<i64>::alloc(1).unwrap();
        let mut table_address = factors.device_ptr();
        let mut count = 2u32;
        let mut output_address = output.device_ptr();
        let mut params = [
            (&mut table_address as *mut u64).cast(),
            (&mut count as *mut u32).cast(),
            (&mut output_address as *mut u64).cast(),
        ];
        let stream = Stream::create().unwrap();
        stream.begin_capture().unwrap();
        function
            .launch_on(&stream, Dim3::x(1), Dim3::x(1), &mut params)
            .unwrap();
        let graph = stream.end_capture().unwrap();
        drop(left);
        drop(right);
        assert!(resolve(left_address, 8).is_ok());
        let executable = graph.instantiate().unwrap();
        executable.launch(&stream).unwrap();
        context.synchronize().unwrap();
        let mut result = [0];
        output.copy_to_slice(&mut result).unwrap();
        assert_eq!(result, [36]);
        drop(executable);
        drop(graph);
        assert!(resolve(left_address, 8).is_err());
        assert!(function
            .launch_on(&stream, Dim3::x(1), Dim3::x(1), &mut params)
            .is_err());
    }

    #[test]
    fn captured_fill_copy_graph_preserves_order() {
        let (_lock, context) = context();
        let source = DeviceBuffer::<u32>::alloc(4).unwrap();
        let destination = DeviceBuffer::<u32>::alloc_zeroed(4).unwrap();
        source.copy_from_slice(&[7, 11, 13, 17]).unwrap();
        let stream = Stream::create().unwrap();
        stream.begin_capture().unwrap();
        stream
            .memset_u32_async(destination.device_ptr(), 0, 4)
            .unwrap();
        stream
            .copy_device_to_device_async(destination.device_ptr(), source.device_ptr(), 16)
            .unwrap();
        let graph = stream.end_capture().unwrap();
        assert_eq!(graph.census().unwrap().memset_nodes, 1);
        assert_eq!(graph.census().unwrap().memcpy_nodes, 1);
        let timing_before = context.inner.execution_timing.get();
        graph.instantiate().unwrap().launch(&stream).unwrap();
        stream.synchronize().unwrap();
        let mut output = [0u32; 4];
        destination.copy_to_slice(&mut output).unwrap();
        assert_eq!(output, [7, 11, 13, 17]);
        context.synchronize().unwrap();
        let timing = context.inner.execution_timing.get();
        assert_eq!(
            timing.completed_command_buffers,
            timing_before.completed_command_buffers + 1
        );
        assert!(timing.unavailable_timestamps <= timing.completed_command_buffers);
        assert!(timing.gpu_seconds.is_finite() && timing.gpu_seconds >= 0.0);
        context.synchronize().unwrap();
        assert_eq!(context.inner.execution_timing.get(), timing);
    }

    #[test]
    fn captured_parallel_grid_preserves_all_coordinates_and_rejects_invalid_geometry() {
        let (_lock, context) = context();
        let module = Module::load_metal(
            r#"
            #include <metal_stdlib>
            using namespace metal;
            kernel void test_grid(device uint *output [[buffer(0)]],
                constant uint &n [[buffer(1)]], uint gid [[thread_position_in_grid]]) {
                if (gid < n) output[gid] = 3u * gid + 7u;
            }
        "#,
        )
        .unwrap();
        let function = module.function("test_grid").unwrap();
        let output = DeviceBuffer::<u32>::alloc_zeroed(73).unwrap();
        let stream = Stream::create().unwrap();
        let mut address = output.device_ptr();
        let mut count = 73_u32;
        let mut params = [
            (&mut address as *mut u64).cast(),
            (&mut count as *mut u32).cast(),
        ];
        assert!(function
            .launch_on(&stream, Dim3::x(0), Dim3::x(32), &mut params)
            .is_err());
        assert!(function
            .launch_on(
                &stream,
                Dim3::x(1),
                Dim3::x(function.max_threads_per_block().unwrap() + 1),
                &mut params
            )
            .is_err());
        stream.begin_capture().unwrap();
        function
            .launch_on(&stream, Dim3::x(3), Dim3::x(32), &mut params)
            .unwrap();
        let graph = stream.end_capture().unwrap();
        graph.instantiate().unwrap().launch(&stream).unwrap();
        context.synchronize().unwrap();
        let mut returned = [0_u32; 73];
        output.copy_to_slice(&mut returned).unwrap();
        assert_eq!(returned, std::array::from_fn(|i| 3 * i as u32 + 7));
    }

    #[test]
    fn dropped_capture_aborts_and_next_command_is_live() {
        let (_lock, context) = context();
        let buffer = DeviceBuffer::<u32>::alloc_zeroed(1).unwrap();
        {
            let stream = Stream::create().unwrap();
            stream.begin_capture().unwrap();
        }
        let stream = Stream::create().unwrap();
        stream.memset_u32_async(buffer.device_ptr(), 0, 1).unwrap();
        stream.synchronize().unwrap();
        context.synchronize().unwrap();
    }

    #[test]
    fn context_and_overlap_refusals_are_explicit() {
        let (_lock, context_one) = context();
        let buffer = DeviceBuffer::<u32>::alloc(4).unwrap();
        let foreign = {
            let device = Device::get(0).unwrap();
            Context::create(&device).unwrap()
        };
        let stream = Stream::create().unwrap();
        assert!(stream.memset_u32_async(buffer.device_ptr(), 0, 1).is_err());
        assert!(buffer.copy_range_from_buffer(1, &buffer, 0, 2).is_err());
        foreign.synchronize().unwrap();
        drop(context_one);
    }

    #[test]
    fn unsupported_operations_remain_refusals() {
        let (_lock, _context) = context();
        assert!(Module::load_ptx(&[]).is_err());
        assert!(PinnedHost::alloc(16).is_err());
        assert!(VirtualDeviceBuffer::<u32>::reserve(0, 4096, 4096).is_err());
    }

    #[test]
    fn repeated_alloc_command_drop_releases_shared_buffers() {
        let (_lock, context) = context();
        let device = Device::get(0).unwrap();
        let baseline = device.inner.current_allocated_size() as usize;
        for _ in 0..64 {
            let buffer = DeviceBuffer::<u32>::alloc(1024).unwrap();
            buffer.copy_from_slice(&[0xA5A5_5A5A; 1024]).unwrap();
            let mut returned = [0u32; 1024];
            buffer.copy_to_slice(&mut returned).unwrap();
            assert_eq!(returned[0], 0xA5A5_5A5A);
        }
        context.synchronize().unwrap();
        let after = device.inner.current_allocated_size() as usize;
        assert!(
            after <= baseline + 4096,
            "Metal allocation did not return near baseline: {baseline} -> {after}"
        );
    }
}
