//! Exact CUDA realization of finite receiver-aperture conic support.
//!
//! CUDA owns allocation, launch, and return only. Continuous conics are
//! transformed into the terminal chart on the host with exact rationals,
//! denominators are cleared, and a conservative arbitrary-precision preflight
//! admits exact native signed i128 device arithmetic. The changing local-star
//! witness disproved the present hand-written wider-limb CUDA operators for
//! both conics and transported segments, so a primitive outside that admitted
//! carrier is evaluated by the same exact host law and merged before
//! whole-face parity admission; it is never rounded or allowed to terminate
//! the frame. The host law substitutes the terminal chart once and conducts
//! integer/projective support; the retained rational implementation is its
//! independent authority. Exact conic coefficients cross the host/card seam
//! in a 128-bit signed-magnitude carrier. The card classifies each finite
//! aperture member independently; it does not propagate through display
//! adjacency and it does not evaluate floating point. Admission compares the
//! two exact carriers on their **exact work vectors** — figures derived from
//! the material and the declared aperture that reproduce bit-for-bit in any
//! frame — and never on the wall clock that watched them. Where the work
//! vector does not separate them, the admission is `Open` and **both carriers
//! stay retained**; it never prefers CUDA by device presence and it never
//! breaks a tie on a timing sample.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::ffi::{CStr, c_char, c_void};
use std::ptr;
use std::time::Instant;

use num_bigint::{BigInt, BigUint};
use num_traits::{Signed, ToPrimitive, Zero};
use relational_geometry::ReceiverId;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::exact_value::ExactOrdering;
use crate::{
    ContinuousPresentation, CpuExecutor, PresentationAddress, PresentationError,
    PresentedPrimitiveKey, PrimitiveApertureTrace, ReceiverApertureTrace, ReceiverPrimitive,
    TerminalMatrixSpec, terminal_integer_conic_coefficients, trace_receivers_aperture_with_cpu,
};

const CUDA_SUCCESS: i32 = 0;
/// **The launch geometry, read off the device and the kernel — never authored.**
///
/// This module carried `const THREADS_PER_BLOCK: u32 = 128` until 2026-08-10, dispositioned `ABI`
/// in `meta/AUTHORED_LEVELS.tsv` with the reason *"CUDA launch geometry, fixed by the device
/// interface."* **That reason was false.** Launch geometry is queryable, and `soma/mount` has
/// derived it correctly all along: `min(the function's own MAX_THREADS_PER_BLOCK, the device's)`,
/// grid from the work extent, refused rather than clipped when it exceeds the grid aperture.
///
/// This is a second implementation of that derivation, and the duplication is **forced**, not
/// chosen: `soma/life` depends on `holonic-engine`, so the engine cannot depend on `soma/mount`
/// without a Cargo cycle (`blueprint/THE_ASSEMBLY.md` F1). Saying so is better than either
/// pretending the pin was ABI or pretending the two owners could be one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DerivedLaunch {
    /// Threads per block: the smaller of what the kernel admits and what the device admits, taken
    /// down to a whole number of warps because a partial warp leaves lanes idle.
    pub block_x: u32,
    /// The device's own ceiling on the X grid dimension. A work extent past it is refused by name.
    pub max_grid_x: u32,
    /// The device's warp size, as the device stated it.
    pub warp: u32,
}

impl DerivedLaunch {
    /// Grid for one flat work extent, or the refusal naming what could not be covered.
    fn grid_for(&self, work: u32) -> Result<u32, CudaApertureError> {
        let blocks = work.div_ceil(self.block_x.max(1));
        if blocks > self.max_grid_x {
            return Err(CudaApertureError::ExtentOverflow);
        }
        Ok(blocks)
    }
}

/// `CUdevice_attribute` and `CUfunction_attribute` selectors from `cuda.h`. THESE are ABI: the
/// integers are fixed by the foreign interface and a different value asks a different question.
const DEVICE_MAX_THREADS_PER_BLOCK: i32 = 1;
const DEVICE_MAX_GRID_DIM_X: i32 = 5;
const DEVICE_WARP_SIZE: i32 = 10;
const FUNCTION_MAX_THREADS_PER_BLOCK: i32 = 0;
const TILE_EDGE: u32 = 16;
/// Largest exact intermediate carried by the compiled device aperture.
///
/// This is a physical aperture of the present CUDA program, not a bound on
/// holonic coordinates. Wider terminal faces must be re-charted or refused;
/// they must never silently become a host rendering path.
const MAX_DEVICE_INTERMEDIATE_BITS: u64 = 384;
const PTX: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/exact_conic_support.ptx"));

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
    fn cuFuncGetAttribute(value: *mut i32, attribute: i32, function: CuFunction) -> i32;
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
    fn cuMemsetD8_v2(destination: CuDevicePtr, value: u8, count: usize) -> i32;
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

fn driver(code: i32, operation: &'static str) -> Result<(), CudaApertureError> {
    if code == CUDA_SUCCESS {
        Ok(())
    } else {
        Err(CudaApertureError::Driver {
            operation,
            code,
            name: driver_text(cuGetErrorName, code),
            message: driver_text(cuGetErrorString, code),
        })
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PackedExactCoefficient {
    lower: u64,
    upper: u64,
    negative: u32,
    reserved: u32,
}

const _: () = assert!(std::mem::size_of::<PackedExactCoefficient>() == 24);

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PackedExactConic {
    xx: PackedExactCoefficient,
    xy: PackedExactCoefficient,
    yy: PackedExactCoefficient,
    x: PackedExactCoefficient,
    y: PackedExactCoefficient,
    constant: PackedExactCoefficient,
    primitive: u32,
    required_bits: u32,
}

const _: () = assert!(std::mem::size_of::<PackedExactConic>() == 152);

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PackedExactSegment {
    line_a: PackedExactCoefficient,
    line_b: PackedExactCoefficient,
    line_c: PackedExactCoefficient,
    bound_left: u32,
    bound_top: u32,
    bound_right: u32,
    bound_bottom: u32,
    primitive: u32,
    required_bits: u32,
}

const _: () = assert!(std::mem::size_of::<PackedExactSegment>() == 96);

struct DeviceAllocation {
    pointer: CuDevicePtr,
}

impl DeviceAllocation {
    fn new(bytes: usize) -> Result<Self, CudaApertureError> {
        let mut pointer = 0;
        // SAFETY: the active CUDA context owns the returned device allocation.
        unsafe { driver(cuMemAlloc_v2(&mut pointer, bytes.max(1)), "cuMemAlloc_v2")? };
        Ok(Self { pointer })
    }
}

impl Drop for DeviceAllocation {
    fn drop(&mut self) {
        // SAFETY: this allocation is owned by the active context; drop is
        // best-effort because Rust destructors cannot return driver errors.
        unsafe {
            let _ = cuMemFree_v2(self.pointer);
        }
    }
}

pub struct CudaApertureExecutor {
    context: CuContext,
    module: CuModule,
    conic_function: CuFunction,
    segment_function: CuFunction,
    _conic_function_i192: CuFunction,
    _segment_function_i192: CuFunction,
    _conic_function_i256: CuFunction,
    _segment_function_i256: CuFunction,
    _conic_function_i128: CuFunction,
    _segment_function_i128: CuFunction,
    device_name: String,
    /// The launch geometry this device and these kernels admit. Derived at mount; nothing authored.
    launch: DerivedLaunch,
    /// The receiver's declared exchange between kinds of work. `None` means undeclared, and an
    /// undeclared metric admits `CarrierAdmission::Open` — both carriers retained.
    declared_metric: Option<DeclaredCarrierMetric>,
    /// Whether the device was driving a display. Declared by the caller; nothing here probes it.
    display_frame: DisplayFrame,
}

impl CudaApertureExecutor {
    pub fn new() -> Result<Self, CudaApertureError> {
        // SAFETY: every raw result and returned handle is checked before use.
        unsafe {
            driver(cuInit(0), "cuInit")?;
            let mut count = 0;
            driver(cuDeviceGetCount(&mut count), "cuDeviceGetCount")?;
            if count <= 0 {
                return Err(CudaApertureError::NoDevice);
            }
            let mut device = 0;
            driver(cuDeviceGet(&mut device, 0), "cuDeviceGet")?;
            let mut name = [0_i8; 256];
            driver(
                cuDeviceGetName(name.as_mut_ptr(), name.len() as i32, device),
                "cuDeviceGetName",
            )?;
            let device_name = CStr::from_ptr(name.as_ptr()).to_string_lossy().into_owned();
            let device_attribute =
                |selector: i32, operation: &'static str| -> Result<u32, CudaApertureError> {
                    let mut value = 0i32;
                    driver(
                        cuDeviceGetAttribute(&mut value, selector, device),
                        operation,
                    )?;
                    Ok(value.max(0) as u32)
                };
            let device_block = device_attribute(
                DEVICE_MAX_THREADS_PER_BLOCK,
                "cuDeviceGetAttribute(MAX_THREADS_PER_BLOCK)",
            )?;
            let max_grid_x = device_attribute(
                DEVICE_MAX_GRID_DIM_X,
                "cuDeviceGetAttribute(MAX_GRID_DIM_X)",
            )?;
            let warp =
                device_attribute(DEVICE_WARP_SIZE, "cuDeviceGetAttribute(WARP_SIZE)")?.max(1);
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
            let mut conic_function = ptr::null_mut();
            let conic_symbol = c"exact_conic_support";
            if let Err(error) = driver(
                cuModuleGetFunction(&mut conic_function, module, conic_symbol.as_ptr()),
                "cuModuleGetFunction(exact_conic_support)",
            ) {
                let _ = cuModuleUnload(module);
                let _ = cuCtxDestroy_v2(context);
                return Err(error);
            }
            let mut segment_function = ptr::null_mut();
            let segment_symbol = c"exact_segment_support";
            if let Err(error) = driver(
                cuModuleGetFunction(&mut segment_function, module, segment_symbol.as_ptr()),
                "cuModuleGetFunction(exact_segment_support)",
            ) {
                let _ = cuModuleUnload(module);
                let _ = cuCtxDestroy_v2(context);
                return Err(error);
            }
            let mut conic_function_i128 = ptr::null_mut();
            let mut conic_function_i192 = ptr::null_mut();
            let conic_symbol_i192 = c"exact_conic_support_i192";
            if let Err(error) = driver(
                cuModuleGetFunction(&mut conic_function_i192, module, conic_symbol_i192.as_ptr()),
                "cuModuleGetFunction(exact_conic_support_i192)",
            ) {
                let _ = cuModuleUnload(module);
                let _ = cuCtxDestroy_v2(context);
                return Err(error);
            }
            let mut segment_function_i192 = ptr::null_mut();
            let segment_symbol_i192 = c"exact_segment_support_i192";
            if let Err(error) = driver(
                cuModuleGetFunction(
                    &mut segment_function_i192,
                    module,
                    segment_symbol_i192.as_ptr(),
                ),
                "cuModuleGetFunction(exact_segment_support_i192)",
            ) {
                let _ = cuModuleUnload(module);
                let _ = cuCtxDestroy_v2(context);
                return Err(error);
            }
            let mut conic_function_i256 = ptr::null_mut();
            let conic_symbol_i256 = c"exact_conic_support_i256";
            if let Err(error) = driver(
                cuModuleGetFunction(&mut conic_function_i256, module, conic_symbol_i256.as_ptr()),
                "cuModuleGetFunction(exact_conic_support_i256)",
            ) {
                let _ = cuModuleUnload(module);
                let _ = cuCtxDestroy_v2(context);
                return Err(error);
            }
            let mut segment_function_i256 = ptr::null_mut();
            let segment_symbol_i256 = c"exact_segment_support_i256";
            if let Err(error) = driver(
                cuModuleGetFunction(
                    &mut segment_function_i256,
                    module,
                    segment_symbol_i256.as_ptr(),
                ),
                "cuModuleGetFunction(exact_segment_support_i256)",
            ) {
                let _ = cuModuleUnload(module);
                let _ = cuCtxDestroy_v2(context);
                return Err(error);
            }
            let conic_symbol_i128 = c"exact_conic_support_i128";
            if let Err(error) = driver(
                cuModuleGetFunction(&mut conic_function_i128, module, conic_symbol_i128.as_ptr()),
                "cuModuleGetFunction(exact_conic_support_i128)",
            ) {
                let _ = cuModuleUnload(module);
                let _ = cuCtxDestroy_v2(context);
                return Err(error);
            }
            let mut segment_function_i128 = ptr::null_mut();
            let segment_symbol_i128 = c"exact_segment_support_i128";
            if let Err(error) = driver(
                cuModuleGetFunction(
                    &mut segment_function_i128,
                    module,
                    segment_symbol_i128.as_ptr(),
                ),
                "cuModuleGetFunction(exact_segment_support_i128)",
            ) {
                let _ = cuModuleUnload(module);
                let _ = cuCtxDestroy_v2(context);
                return Err(error);
            }
            Ok(Self {
                context,
                module,
                conic_function,
                segment_function,
                _conic_function_i192: conic_function_i192,
                _segment_function_i192: segment_function_i192,
                _conic_function_i256: conic_function_i256,
                _segment_function_i256: segment_function_i256,
                _conic_function_i128: conic_function_i128,
                _segment_function_i128: segment_function_i128,
                device_name,
                launch: {
                    // The kernels launched are the conic and segment pair; the block must fit
                    // whichever of the two admits fewer threads, and the device's own ceiling.
                    let mut kernel_block = device_block;
                    for function in [conic_function, segment_function] {
                        let mut value = 0i32;
                        driver(
                            cuFuncGetAttribute(
                                &mut value,
                                FUNCTION_MAX_THREADS_PER_BLOCK,
                                function,
                            ),
                            "cuFuncGetAttribute(MAX_THREADS_PER_BLOCK)",
                        )?;
                        kernel_block = kernel_block.min(value.max(0) as u32);
                    }
                    // Down to a whole number of warps: a partial warp issues with idle lanes.
                    let block_x = (kernel_block / warp).max(1) * warp;
                    DerivedLaunch {
                        block_x,
                        max_grid_x,
                        warp,
                    }
                },
                declared_metric: None,
                display_frame: DisplayFrame::Undeclared,
            })
        }
    }

    pub fn device_name(&self) -> &str {
        &self.device_name
    }

    pub fn trace(
        &self,
        presentation: &ContinuousPresentation,
        specification: &TerminalMatrixSpec,
        receivers: &BTreeSet<ReceiverId>,
        host_executor: &CpuExecutor,
    ) -> Result<
        (
            BTreeMap<ReceiverId, ReceiverApertureTrace>,
            CudaApertureReceipt,
        ),
        CudaApertureError,
    > {
        self.make_current()?;
        let total_started = Instant::now();
        let selected = presentation
            .primitives
            .iter()
            .filter(|presented| receivers.contains(&presented.receiver))
            .collect::<Vec<_>>();
        let mut packed_conics = Vec::new();
        let mut packed_segments = Vec::new();
        let mut device_selected_ordinals = Vec::new();
        let mut host_primitives = Vec::new();
        let mut required_intermediate_bits = 0_u64;
        for (primitive_ordinal, presented) in selected.iter().enumerate() {
            let primitive =
                u32::try_from(primitive_ordinal).map_err(|_| CudaApertureError::ExtentOverflow)?;
            let packed = (|| {
                let mut conics = Vec::new();
                let mut segments = Vec::new();
                match &presented.primitive {
                    ReceiverPrimitive::Conic(conic) => {
                        conics.push(pack_conic(&conic.form, specification, primitive)?);
                    }
                    ReceiverPrimitive::Triangle(triangle) => {
                        for edge in triangle.vertices.windows(2) {
                            segments.extend(pack_projective_segment(
                                &edge[0],
                                &edge[1],
                                specification,
                                primitive,
                            )?);
                        }
                        segments.extend(pack_projective_segment(
                            &triangle.vertices[2],
                            &triangle.vertices[0],
                            specification,
                            primitive,
                        )?);
                    }
                    ReceiverPrimitive::Thread(thread) => {
                        for edge in thread.vertices.windows(2) {
                            segments.extend(pack_projective_segment(
                                &edge[0],
                                &edge[1],
                                specification,
                                primitive,
                            )?);
                        }
                        if thread.closed && thread.vertices.len() > 1 {
                            segments.extend(pack_projective_segment(
                                thread.vertices.last().expect("a closed thread has a tail"),
                                &thread.vertices[0],
                                specification,
                                primitive,
                            )?);
                        }
                    }
                }
                Ok::<_, CudaApertureError>((conics, segments))
            })();
            match packed {
                Ok((conics, segments)) => {
                    let primitive_bits = conics
                        .iter()
                        .map(|conic| conic.required_bits)
                        .chain(segments.iter().map(|segment| segment.required_bits))
                        .max()
                        .unwrap_or(0);
                    required_intermediate_bits =
                        required_intermediate_bits.max(u64::from(primitive_bits));
                    if u64::from(primitive_bits) <= MAX_DEVICE_INTERMEDIATE_BITS {
                        let device_ordinal = u32::try_from(device_selected_ordinals.len())
                            .map_err(|_| CudaApertureError::ExtentOverflow)?;
                        device_selected_ordinals.push(primitive_ordinal);
                        packed_conics.extend(conics.into_iter().map(|mut conic| {
                            conic.primitive = device_ordinal;
                            conic
                        }));
                        packed_segments.extend(segments.into_iter().map(|mut segment| {
                            segment.primitive = device_ordinal;
                            segment
                        }));
                    } else {
                        host_primitives.push((**presented).clone());
                    }
                }
                Err(CudaApertureError::IntegerRange { required_bits, .. }) => {
                    if std::env::var_os("HOLONIC_CUDA_CARRIER_DIAG").is_some() {
                        eprintln!(
                            "carrier-open primitive={primitive_ordinal} species={} coefficient-bits={required_bits}",
                            match &presented.primitive {
                                ReceiverPrimitive::Conic(_) => "conic",
                                ReceiverPrimitive::Triangle(_) => "triangle",
                                ReceiverPrimitive::Thread(_) => "thread",
                            },
                        );
                    }
                    required_intermediate_bits = required_intermediate_bits.max(required_bits);
                    host_primitives.push((**presented).clone());
                }
                Err(error) => return Err(error),
            }
        }
        let selection_pack_nanoseconds = total_started.elapsed().as_nanos();
        let _required_device_bits = packed_conics
            .iter()
            .map(|conic| conic.required_bits)
            .chain(packed_segments.iter().map(|segment| segment.required_bits))
            .max()
            .unwrap_or(0);
        let (conic_function, segment_function, device_arithmetic) =
            (self.conic_function, self.segment_function, "signed 384-bit");
        let pixel_count = specification
            .width
            .checked_mul(specification.height)
            .ok_or(CudaApertureError::ExtentOverflow)?;
        let support_word_count = usize::try_from(pixel_count.div_ceil(u32::BITS))
            .map_err(|_| CudaApertureError::ExtentOverflow)?;
        let output_count = support_word_count
            .checked_mul(device_selected_ordinals.len())
            .ok_or(CudaApertureError::ExtentOverflow)?;

        let device_prepare_started = Instant::now();
        let conic_allocation =
            DeviceAllocation::new(packed_conics.len() * std::mem::size_of::<PackedExactConic>())?;
        let segment_allocation = DeviceAllocation::new(
            packed_segments.len() * std::mem::size_of::<PackedExactSegment>(),
        )?;
        let output_allocation = DeviceAllocation::new(output_count * std::mem::size_of::<u32>())?;
        let query_allocation =
            DeviceAllocation::new(device_selected_ordinals.len() * std::mem::size_of::<u64>())?;
        if !packed_conics.is_empty() {
            // SAFETY: source length exactly matches the allocated device span.
            unsafe {
                driver(
                    cuMemcpyHtoD_v2(
                        conic_allocation.pointer,
                        packed_conics.as_ptr().cast(),
                        packed_conics.len() * std::mem::size_of::<PackedExactConic>(),
                    ),
                    "cuMemcpyHtoD_v2(conics)",
                )?
            };
        }
        if !packed_segments.is_empty() {
            // SAFETY: source length exactly matches the allocated device span.
            unsafe {
                driver(
                    cuMemcpyHtoD_v2(
                        segment_allocation.pointer,
                        packed_segments.as_ptr().cast(),
                        packed_segments.len() * std::mem::size_of::<PackedExactSegment>(),
                    ),
                    "cuMemcpyHtoD_v2(segments)",
                )?
            };
        }
        let mut output = vec![0_u32; output_count];
        let mut query_counts = vec![0_u64; device_selected_ordinals.len()];
        // Sparse local-section fibers write only actual support. Clear the
        // bounded consequence carrier so inherited device state cannot enter.
        unsafe {
            driver(
                cuMemsetD8_v2(
                    output_allocation.pointer,
                    0,
                    output_count * std::mem::size_of::<u32>(),
                ),
                "cuMemsetD8_v2(output)",
            )?;
            driver(
                cuMemsetD8_v2(
                    query_allocation.pointer,
                    0,
                    device_selected_ordinals.len() * std::mem::size_of::<u64>(),
                ),
                "cuMemsetD8_v2(query)",
            )?;
        }
        let device_prepare_nanoseconds = device_prepare_started.elapsed().as_nanos();
        let mut conic_pointer = conic_allocation.pointer;
        let mut segment_pointer = segment_allocation.pointer;
        let mut output_pointer = output_allocation.pointer;
        let mut query_pointer = query_allocation.pointer;
        let mut width = specification.width;
        let mut height = specification.height;
        let mut conic_count =
            u32::try_from(packed_conics.len()).map_err(|_| CudaApertureError::ExtentOverflow)?;
        let mut segment_count =
            u32::try_from(packed_segments.len()).map_err(|_| CudaApertureError::ExtentOverflow)?;
        let receiver_count =
            u32::try_from(receivers.len()).map_err(|_| CudaApertureError::ExtentOverflow)?;
        let mut conic_arguments = [
            (&mut conic_pointer as *mut CuDevicePtr).cast::<c_void>(),
            (&mut output_pointer as *mut CuDevicePtr).cast::<c_void>(),
            (&mut query_pointer as *mut CuDevicePtr).cast::<c_void>(),
            (&mut width as *mut u32).cast::<c_void>(),
            (&mut height as *mut u32).cast::<c_void>(),
            (&mut conic_count as *mut u32).cast::<c_void>(),
        ];
        let mut segment_arguments = [
            (&mut segment_pointer as *mut CuDevicePtr).cast::<c_void>(),
            (&mut output_pointer as *mut CuDevicePtr).cast::<c_void>(),
            (&mut query_pointer as *mut CuDevicePtr).cast::<c_void>(),
            (&mut width as *mut u32).cast::<c_void>(),
            (&mut height as *mut u32).cast::<c_void>(),
            (&mut segment_count as *mut u32).cast::<c_void>(),
        ];
        let tile_columns = width.div_ceil(TILE_EDGE);
        let tile_rows = height.div_ceil(TILE_EDGE);
        let tile_count = tile_columns
            .checked_mul(tile_rows)
            .ok_or(CudaApertureError::ExtentOverflow)?;
        let conic_work = tile_count
            .checked_mul(conic_count)
            .ok_or(CudaApertureError::ExtentOverflow)?;
        let segment_work = tile_count
            .checked_mul(segment_count)
            .ok_or(CudaApertureError::ExtentOverflow)?;
        let device_execute_started = Instant::now();
        // SAFETY: the PTX signature and the six argument carriers above are
        // pinned by the shared repr(C) wire and checked extents.
        if conic_work > 0 {
            unsafe {
                driver(
                    cuLaunchKernel(
                        conic_function,
                        self.launch.grid_for(conic_work)?,
                        1,
                        1,
                        self.launch.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        conic_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    ),
                    "cuLaunchKernel(exact_conic_support)",
                )?;
            }
        }
        if segment_work > 0 {
            unsafe {
                driver(
                    cuLaunchKernel(
                        segment_function,
                        self.launch.grid_for(segment_work)?,
                        1,
                        1,
                        self.launch.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        segment_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    ),
                    "cuLaunchKernel(exact_segment_support)",
                )?;
            }
        }
        let device_launch_nanoseconds = device_execute_started.elapsed().as_nanos();
        let host_primitive_count = host_primitives.len();
        let host_conic_count = host_primitives
            .iter()
            .filter(|presented| matches!(&presented.primitive, ReceiverPrimitive::Conic(_)))
            .count();
        let mut host_workers = BigUint::zero();
        let mut host_trace_nanoseconds = 0_u128;
        let host_result = if host_primitives.is_empty() {
            None
        } else {
            let mut host_presentation = presentation.clone();
            host_presentation.primitives = host_primitives;
            let host_trace_started = Instant::now();
            let result = trace_receivers_aperture_with_cpu(
                &host_presentation,
                specification,
                receivers,
                host_executor,
            )?;
            host_trace_nanoseconds = host_trace_started.elapsed().as_nanos();
            host_workers = result.1.workers_used.clone();
            Some(result.0)
        };
        let device_wait_started = Instant::now();
        unsafe {
            driver(cuCtxSynchronize(), "cuCtxSynchronize")?;
        }
        let device_execute_nanoseconds =
            device_launch_nanoseconds + device_wait_started.elapsed().as_nanos();
        let device_download_started = Instant::now();
        unsafe {
            driver(
                cuMemcpyDtoH_v2(
                    output.as_mut_ptr().cast(),
                    output_allocation.pointer,
                    output.len() * std::mem::size_of::<u32>(),
                ),
                "cuMemcpyDtoH_v2(support)",
            )?;
            driver(
                cuMemcpyDtoH_v2(
                    query_counts.as_mut_ptr().cast(),
                    query_allocation.pointer,
                    query_counts.len() * std::mem::size_of::<u64>(),
                ),
                "cuMemcpyDtoH_v2(query)",
            )?;
        }
        let device_download_nanoseconds = device_download_started.elapsed().as_nanos();

        let device_decode_started = Instant::now();
        let mut primitive_sections = BTreeMap::new();
        for (device_primitive, selected_ordinal) in
            device_selected_ordinals.iter().copied().enumerate()
        {
            let presented = selected[selected_ordinal];
            let key = PresentedPrimitiveKey {
                receiver: presented.receiver,
                primitive: presented.primitive.id(),
            };
            let offset = device_primitive * support_word_count;
            let addresses = decode_support_words(
                &output[offset..offset + support_word_count],
                specification.width,
                specification.height,
            )?;
            if primitive_sections
                .insert(
                    key,
                    PrimitiveApertureTrace {
                        key,
                        addresses,
                        exact_support_queries: BigUint::from(query_counts[device_primitive]),
                    },
                )
                .is_some()
            {
                return Err(CudaApertureError::Presentation(
                    PresentationError::DuplicatePrimitiveTrace(key.receiver),
                ));
            }
        }
        let device_decode_nanoseconds = device_decode_started.elapsed().as_nanos();
        let device_exact_support_evaluations = BigUint::from(query_counts.into_iter().sum::<u64>());
        let mut host_exact_support_evaluations = BigUint::zero();
        let mut exact_support_evaluations = device_exact_support_evaluations.clone();
        let mut host_merge_nanoseconds = 0_u128;
        if let Some(host_traces) = host_result {
            let host_merge_started = Instant::now();
            for host_trace in host_traces.into_values() {
                exact_support_evaluations += &host_trace.exact_support_queries;
                host_exact_support_evaluations += &host_trace.exact_support_queries;
                for section in host_trace.primitive_sections.into_values() {
                    let key = section.key;
                    if primitive_sections.insert(key, section).is_some() {
                        return Err(CudaApertureError::Presentation(
                            PresentationError::DuplicatePrimitiveTrace(key.receiver),
                        ));
                    }
                }
            }
            host_merge_nanoseconds = host_merge_started.elapsed().as_nanos();
        }
        let mut sections_by_receiver = receivers
            .iter()
            .copied()
            .map(|receiver| (receiver, Vec::new()))
            .collect::<BTreeMap<_, _>>();
        for section in primitive_sections.into_values() {
            sections_by_receiver
                .get_mut(&section.key.receiver)
                .expect("every selected primitive belongs to an admitted receiver")
                .push(section);
        }
        let traces = sections_by_receiver
            .into_iter()
            .map(|(receiver, sections)| {
                Ok((
                    receiver,
                    ReceiverApertureTrace::from_primitive_sections(receiver, sections)?,
                ))
            })
            .collect::<Result<BTreeMap<_, _>, PresentationError>>()?;
        let arithmetic = if host_primitive_count == 0 {
            device_arithmetic.to_owned()
        } else if device_selected_ordinals.is_empty() {
            "exact host integer-projective".to_owned()
        } else {
            format!("{device_arithmetic} CUDA + exact host integer-projective")
        };
        Ok((
            traces,
            CudaApertureReceipt {
                schema: "holonic-engine.cuda-aperture.v1".to_owned(),
                device: self.device_name.clone(),
                receivers: BigUint::from(receiver_count),
                selected_primitives: BigUint::from(selected.len()),
                device_primitives: BigUint::from(device_selected_ordinals.len()),
                conics: BigUint::from(conic_count),
                segments: BigUint::from(segment_count),
                host_primitives: BigUint::from(host_primitive_count),
                host_conics: BigUint::from(host_conic_count),
                host_linear_primitives: BigUint::from(host_primitive_count - host_conic_count),
                aperture_members: BigUint::from(pixel_count),
                device_output_bytes: BigUint::from(output_count * std::mem::size_of::<u32>()),
                device_threads: BigUint::from(conic_work) + BigUint::from(segment_work),
                exact_support_evaluations,
                device_exact_support_evaluations,
                host_exact_support_evaluations,
                intermediate_bits: BigUint::from(required_intermediate_bits),
                device_arithmetic: arithmetic,
                host_workers,
                selection_pack_nanoseconds,
                device_prepare_nanoseconds,
                device_execute_nanoseconds,
                device_download_nanoseconds,
                device_decode_nanoseconds,
                host_trace_nanoseconds,
                host_merge_nanoseconds,
                wall_nanoseconds: total_started.elapsed().as_nanos(),
                host_parity: false,
                execution_backend: ApertureExecutionBackend::HybridCuda.label().to_owned(),
                admission_candidate_nanoseconds: 0,
                admission_authority_nanoseconds: 0,
                admission: CarrierAdmission::Open,
                work_ordering: ExactOrdering::Open,
                authority_work: CarrierWork::default(),
                candidate_work: CarrierWork::default(),
                display_frame: self.display_frame,
            },
        ))
    }

    pub fn admit(
        self,
        presentation: &ContinuousPresentation,
        specification: &TerminalMatrixSpec,
        receivers: &BTreeSet<ReceiverId>,
        host_executor: &CpuExecutor,
    ) -> Result<
        (
            AdmittedCudaApertureExecutor,
            BTreeMap<ReceiverId, ReceiverApertureTrace>,
            CudaApertureReceipt,
        ),
        CudaApertureError,
    > {
        let (candidate, mut receipt) =
            self.trace(presentation, specification, receivers, host_executor)?;
        let authority_started = Instant::now();
        let (authority, authority_execution) = trace_receivers_aperture_with_cpu(
            presentation,
            specification,
            receivers,
            host_executor,
        )?;
        let authority_nanoseconds = authority_started.elapsed().as_nanos();
        let exact = candidate.iter().all(|(receiver, candidate)| {
            authority
                .get(receiver)
                .is_some_and(|authority| candidate.has_same_exact_support(authority))
        }) && candidate.len() == authority.len();
        if !exact {
            return Err(CudaApertureError::ParityRefused);
        }
        let candidate_nanoseconds = receipt.wall_nanoseconds;

        // Parity has just proved the two carriers return the same exact support for these
        // receivers. Having proved they cannot be told apart, the admission must not resolve the
        // choice by consulting a coordinate that is not in the receiver family at all — which is
        // what `authority_nanoseconds < candidate_nanoseconds` did until 2026-08-08, permanently
        // selecting a carrier from one unrepeated wall-clock sample taken on a contended machine.
        //
        // Cost is exact work. Every quantity below is derived from the material and the declared
        // aperture and reproduces bit-for-bit on any machine, in any frame — headless or scanning
        // out a desktop.
        let candidate_work = CarrierWork::of_candidate(&receipt);
        let authority_work = CarrierWork::of_host_authority(&receipt);
        // The four-state exact ordering of the two work vectors, taken with nothing declared. It
        // is retained on the receipt whether or not it decided, because `Equal` (a mirror) and
        // `Open` (incomparable kinds of work) are different states that conduct identically.
        let work_ordering = candidate_work.order_against(&authority_work);
        let admission = match self.declared_metric.as_ref() {
            Some(metric) => CarrierAdmission::under(metric, &authority_work, &candidate_work),
            None => CarrierAdmission::from_work(&authority_work, &candidate_work),
        };
        let preferred = admission.conducts_through();
        receipt.host_parity = true;
        receipt.admission = admission.clone();
        receipt.work_ordering = work_ordering;
        receipt.authority_work = authority_work;
        receipt.candidate_work = candidate_work;
        receipt.display_frame = self.display_frame;
        receipt.admission_candidate_nanoseconds = candidate_nanoseconds;
        receipt.admission_authority_nanoseconds = authority_nanoseconds;
        let initial = match preferred {
            ApertureExecutionBackend::ExactHost => {
                let required_bits = receipt.intermediate_bits.clone();
                // The host receipt is rebuilt from the host run, so every field carrying the
                // admission's own evidence has to be carried across the swap. Losing it here would
                // leave the branch where the host was admitted unable to say why — which is the
                // branch a reader checks first.
                let carried_admission = std::mem::take(&mut receipt.admission);
                let carried_authority_work = std::mem::take(&mut receipt.authority_work);
                let carried_candidate_work = std::mem::take(&mut receipt.candidate_work);
                receipt = exact_host_receipt(
                    &self.device_name,
                    presentation,
                    specification,
                    receivers,
                    authority_execution.workers_used,
                    &authority,
                    authority_nanoseconds,
                )?;
                receipt.intermediate_bits = required_bits;
                receipt.admission = carried_admission;
                receipt.work_ordering = work_ordering;
                receipt.authority_work = carried_authority_work;
                receipt.candidate_work = carried_candidate_work;
                receipt.display_frame = self.display_frame;
                receipt.admission_candidate_nanoseconds = candidate_nanoseconds;
                receipt.admission_authority_nanoseconds = authority_nanoseconds;
                authority
            }
            ApertureExecutionBackend::HybridCuda => candidate,
        };
        Ok((
            AdmittedCudaApertureExecutor {
                inner: self,
                admission,
            },
            initial,
            receipt,
        ))
    }

    /// Declare the receiver's exchange between kinds of work.
    ///
    /// Without this, [`Self::admit`] falls back to [`CarrierAdmission::from_work`] — the
    /// **metric-free** product order, which decides only when one carrier dominates the other in
    /// every coordinate and returns [`CarrierAdmission::Open`] otherwise, retaining both. That
    /// default is deliberate: an undeclared metric is not a licence to guess, and guessing is what
    /// the wall-clock comparison was. On this executor's own material the two carriers trade host
    /// evaluations against device evaluations plus transferred octets, so the product order is
    /// [`ExactOrdering::Open`] whenever the card did any work at all — which is exactly why a
    /// declaration, and not a clock, is what separates them.
    #[must_use]
    pub fn declaring(mut self, metric: DeclaredCarrierMetric) -> Self {
        self.declared_metric = Some(metric);
        self
    }

    /// Declare whether the device is driving a display, so every nanosecond figure this executor
    /// emits carries the frame it was taken in.
    #[must_use]
    pub fn in_frame(mut self, frame: DisplayFrame) -> Self {
        self.display_frame = frame;
        self
    }

    fn make_current(&self) -> Result<(), CudaApertureError> {
        // SAFETY: this retained executor exclusively owns the context and every handle founded
        // beneath it. CUDA current-context selection is thread-local apparatus, so each public
        // device passage reactivates its owner before touching those handles.
        unsafe { driver(cuCtxSetCurrent(self.context), "cuCtxSetCurrent") }
    }
}

impl Drop for CudaApertureExecutor {
    fn drop(&mut self) {
        // SAFETY: module and context were created together and are destroyed
        // in dependency order. Teardown is best-effort.
        unsafe {
            let _ = cuCtxSetCurrent(self.context);
            let _ = cuModuleUnload(self.module);
            let _ = cuCtxDestroy_v2(self.context);
        }
    }
}

/// The exact work one carrier did, derived from the material and the declared aperture.
///
/// **This is the frame-invariant half of a receipt.** Every field is a `BigUint` computed from the
/// presentation and the specification; none of it moves when the machine is busy, when another
/// process takes a core, or when the device is simultaneously scanning out a desktop. The
/// `*_nanoseconds` fields beside it in [`CudaApertureReceipt`] are the frame-dependent half: they
/// record how long *this* machine took to do exactly this work, which is a lawful measurement and
/// never an admission.
///
/// `CLAUDE.md` §8 — *"Grade the complexity against the source owner, measure both across a changed
/// aperture, and state the bound as a falsifier."* The complexity is this vector. It was already
/// being computed, and was discarded in favour of a clock.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CarrierWork {
    /// Exact support evaluations performed on the host.
    pub host_evaluations: BigUint,
    /// Exact support evaluations performed on the device.
    pub device_evaluations: BigUint,
    /// Octets moved across the device boundary in either direction.
    pub transfer_bytes: BigUint,
    /// Widest intermediate this carrier had to represent exactly.
    pub intermediate_bits: BigUint,
}

impl CarrierWork {
    /// The work the hybrid candidate did, read off its own receipt.
    pub fn of_candidate(receipt: &CudaApertureReceipt) -> Self {
        Self {
            host_evaluations: receipt.host_exact_support_evaluations.clone(),
            device_evaluations: receipt.device_exact_support_evaluations.clone(),
            transfer_bytes: receipt.device_output_bytes.clone(),
            intermediate_bits: receipt.intermediate_bits.clone(),
        }
    }

    /// The work the host authority does on the same material, **predicted from the same receipt
    /// without running it**. The host law evaluates every selected primitive against every
    /// aperture member and moves nothing across a device boundary, so its work is the candidate's
    /// total evaluation count with the split collapsed.
    ///
    /// That this is a *prediction* is what makes the cost law falsifiable (§4.4 of the record):
    /// running the authority either confirms the predicted ordering or refutes it, and a
    /// refutation says the declared law is wrong about this material — information the clock
    /// comparison could not produce at all.
    pub fn of_host_authority(receipt: &CudaApertureReceipt) -> Self {
        Self {
            host_evaluations: receipt.exact_support_evaluations.clone(),
            device_evaluations: BigUint::default(),
            transfer_bytes: BigUint::default(),
            intermediate_bits: receipt.intermediate_bits.clone(),
        }
    }

    /// Order this work vector against another **with no metric at all**, returning the four-state
    /// [`ExactOrdering`] this body already owns at `crates/holonic-engine/src/exact_value.rs`.
    ///
    /// This is the componentwise (product) order, and it is a **partial** order on purpose. A
    /// coordinate here is a kind of work, and the kinds are not interconvertible: a host evaluation
    /// and a device evaluation are different units, and nothing in the material says how many of one
    /// buys one of the other. So:
    ///
    /// - `Less` / `Greater` — one carrier does no more work in **every** coordinate and strictly
    ///   less in at least one. That is domination, and it holds under every monotone metric, so it
    ///   needs no receiver declaration to be read.
    /// - `Equal` — the two vectors coincide. The detour founded nothing.
    /// - `Open` — some coordinate is strictly less and another strictly greater. The carriers are
    ///   **incomparable**, not tied, and **both stay retained**. From `exact_value.rs`'s own
    ///   opening: *"Values which cannot yet be ordered from their exact certificates return `Open`
    ///   rather than falling through to an epsilon comparison."* A wall-clock sample is what falling
    ///   through looked like here.
    ///
    /// `intermediate_bits` participates: it is a width rather than a count, so
    /// [`DeclaredCarrierMetric`] does not price it, but a carrier that had to represent wider
    /// intermediates exactly did strictly more work per evaluation and the product order may say so.
    pub fn order_against(&self, other: &Self) -> ExactOrdering {
        let coordinates = [
            self.host_evaluations.cmp(&other.host_evaluations),
            self.device_evaluations.cmp(&other.device_evaluations),
            self.transfer_bytes.cmp(&other.transfer_bytes),
            self.intermediate_bits.cmp(&other.intermediate_bits),
        ];
        let any_less = coordinates.iter().any(|order| *order == Ordering::Less);
        let any_greater = coordinates.iter().any(|order| *order == Ordering::Greater);
        match (any_less, any_greater) {
            (true, true) => ExactOrdering::Open,
            (true, false) => ExactOrdering::Less,
            (false, true) => ExactOrdering::Greater,
            (false, false) => ExactOrdering::Equal,
        }
    }
}

/// A receiver's declared exchange between kinds of work.
///
/// Host and device evaluations are not the same unit, and nothing in the material says how to
/// trade one for the other. `CLAUDE.md` §13 rule 2: *"`dL` is a covector. It becomes a gradient
/// only under a declared metric: `grad_G L = G⁻¹ dL`, and the metric is a receiver face of
/// standing, so `G` is a receiver's declaration and never a modelling convenience."*
///
/// So the exchange is declared by whoever admits the executor, or it is not declared and the
/// admission returns [`CarrierAdmission::Open`]. It is never inferred from a clock.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeclaredCarrierMetric {
    pub host_evaluation_cost: BigUint,
    pub device_evaluation_cost: BigUint,
    pub transfer_byte_cost: BigUint,
}

impl DeclaredCarrierMetric {
    /// The exact cost this metric assigns to a work vector. Integer throughout; no rounding, no
    /// tolerance, and no comparison that is not exact.
    pub fn cost_of(&self, work: &CarrierWork) -> BigUint {
        &work.host_evaluations * &self.host_evaluation_cost
            + &work.device_evaluations * &self.device_evaluation_cost
            + &work.transfer_bytes * &self.transfer_byte_cost
    }
}

/// The dilation between two carriers, held as the exact pair `(C, d)` and **never divided**.
///
/// `MENO_FORMULA §VIII`, ratified: *"`π_Β` is held HOLONIC — the pair `(C, d)`, NEVER divided into
/// an integer. `8/2` and `4/1` are different holonic states (different arc, different diagonal,
/// different rank); the integer throws that away and re-smuggles the absolute frame."*
///
/// Here the two carriers are the two frames, and that is the only lawful reading — Ledger U:
/// *"dilation is relational, a ratio of frames, never a property of one node."* So there is no
/// per-carrier cost scalar in this type. There is one pair.
///
/// **The host authority is `d`.** It crosses directly: every support evaluated in one place, no
/// split, no transfer, no merge. **The hybrid candidate is `C`.** It detours — packs, dispatches,
/// runs the wide primitives back on the host, downloads, merges. Parity has already proved the two
/// share endpoints, which is exactly what makes them an arc and a chord rather than two unrelated
/// walks.
///
/// `C = d` is the **mirror**: the detour founded nothing.
/// `C ≠ d` is the **founding**: it wound to get there, and whether the winding paid is a question
/// for the receiver that declared the metric, never for a clock.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CarrierDilation {
    /// `C` — the finding-walk. What the hybrid candidate traversed under the declared metric.
    pub arc: BigUint,
    /// `d` — the checking-step. What the host authority crosses directly under the same metric.
    pub chord: BigUint,
}

impl CarrierDilation {
    /// `C = d`. The arc never left the diagonal.
    pub fn is_mirror(&self) -> bool {
        self.arc == self.chord
    }

    /// Order two dilations **without forming either quotient**. `a₁·d₂` against `a₂·d₁` is the
    /// cross-multiplication every exact ratio comparison uses: it never divides and never rounds.
    pub fn cmp_against(&self, other: &Self) -> Ordering {
        (&self.arc * &other.chord).cmp(&(&other.arc * &self.chord))
    }
}

/// Which carrier the body conducts through, carrying the whole dilation rather than a verdict.
///
/// Modelled on `crates/holonic-engine/src/exact_value.rs`'s `ExactOrdering { Less, Equal, Greater,
/// Open }`: *"Values which cannot yet be ordered from their exact certificates return `Open` rather
/// than falling through to an epsilon comparison."*
///
/// Every deciding variant carries the pair. A caller that wants a number may form one; nothing on
/// this path does — §13 rule 2, *plurality is the return; a continuation fiber is not a number.*
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub enum CarrierAdmission {
    /// The arc wound further than the chord, `C > d`: the direct crossing is the shorter walk.
    ///
    /// `dilation` is `None` when no metric was declared and the admission was taken on the
    /// **metric-free** product order instead — there, one carrier dominates the other in every
    /// coordinate, which is a stronger statement than any single metric makes and forms no pair.
    ExactHost { dilation: Option<CarrierDilation> },
    /// The arc is the shorter walk, `C < d`: the detour paid under this receiver's declaration.
    HybridCuda { dilation: Option<CarrierDilation> },
    /// The carriers are not separated. Either no metric was declared and the work vectors are
    /// **incomparable** — [`ExactOrdering::Open`], some coordinate strictly less and another
    /// strictly greater — or the declared metric makes this a **mirror**, `C = d`, the arc never
    /// left the diagonal. **Both stay retained**, and a caller may conduct through either with
    /// [`AdmittedCudaApertureExecutor::trace_through`].
    ///
    /// The receipt's `work_ordering` field tells the two apart: `Equal` is a mirror, `Open` is
    /// incomparability. They conduct the same way and they are not the same state.
    #[default]
    Open,
}

impl CarrierAdmission {
    /// Read the admission off a declared metric and two exact work vectors.
    ///
    /// The metric turns a path into a length, which is what a metric is for. It does not turn two
    /// lengths into a winner — that is the pair's job, and the pair survives into the return.
    pub fn under(
        metric: &DeclaredCarrierMetric,
        authority: &CarrierWork,
        candidate: &CarrierWork,
    ) -> Self {
        let dilation = CarrierDilation {
            arc: metric.cost_of(candidate),
            chord: metric.cost_of(authority),
        };
        match dilation.arc.cmp(&dilation.chord) {
            Ordering::Greater => Self::ExactHost {
                dilation: Some(dilation),
            },
            Ordering::Less => Self::HybridCuda {
                dilation: Some(dilation),
            },
            Ordering::Equal => Self::Open,
        }
    }

    /// Read the admission off the two exact work vectors alone, **with nothing declared**.
    ///
    /// This is [`CarrierWork::order_against`] read as an admission. It decides only on domination —
    /// no more work in any coordinate, strictly less in one — because that is the only separation
    /// available without a receiver's declared exchange between kinds of work. Everything else,
    /// including genuine incomparability, is [`Self::Open`] and retains both carriers.
    ///
    /// An undeclared metric is not a licence to guess. It is also not a licence to refuse a
    /// separation the material already carries.
    pub fn from_work(authority: &CarrierWork, candidate: &CarrierWork) -> Self {
        match candidate.order_against(authority) {
            ExactOrdering::Less => Self::HybridCuda { dilation: None },
            ExactOrdering::Greater => Self::ExactHost { dilation: None },
            ExactOrdering::Equal | ExactOrdering::Open => Self::Open,
        }
    }

    /// The carrier later conduct takes by default.
    ///
    /// Under `Open` this is the host authority, because the host law is the reference every parity
    /// gate is taken against and is available unconditionally. That is a retained-plurality default
    /// and not a hidden preference: [`Self::is_open`] reports it, the receipt carries it, and
    /// `trace_through` conducts the other way on request.
    pub fn conducts_through(&self) -> ApertureExecutionBackend {
        match self {
            Self::HybridCuda { .. } => ApertureExecutionBackend::HybridCuda,
            Self::ExactHost { .. } | Self::Open => ApertureExecutionBackend::ExactHost,
        }
    }

    pub fn is_open(&self) -> bool {
        matches!(self, Self::Open)
    }

    /// The whole pair `(C, d)`, or `None` when nothing was declared to form it against — which
    /// includes a decided admission taken on the metric-free product order.
    pub fn dilation(&self) -> Option<&CarrierDilation> {
        match self {
            Self::ExactHost { dilation } | Self::HybridCuda { dilation } => dilation.as_ref(),
            Self::Open => None,
        }
    }
}
/// Whether the device was driving a display when a timing figure was taken.
///
/// A measurement without its frame is the absolute-frame defect `CLAUDE.md` §0 names. Every timing
/// figure in this repository was taken with the card headless and the desktop idle, so no timing
/// claim here has been falsifiable: there was only ever one frame. Declaring this coordinate is
/// what makes a display-active run a **second frame** rather than corrupted data — the exact work
/// vector must not move between the two, and any nanosecond figure that does was always a machine
/// artifact.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub enum DisplayFrame {
    /// Not declared by the caller. The default, and honest: nothing here probes the device for it.
    #[default]
    Undeclared,
    /// The device was headless.
    Headless,
    /// The device was scanning out at least one display.
    DisplayActive,
}

pub struct AdmittedCudaApertureExecutor {
    inner: CudaApertureExecutor,
    admission: CarrierAdmission,
}

impl AdmittedCudaApertureExecutor {
    pub fn trace(
        &self,
        presentation: &ContinuousPresentation,
        specification: &TerminalMatrixSpec,
        receivers: &BTreeSet<ReceiverId>,
        host_executor: &CpuExecutor,
    ) -> Result<
        (
            BTreeMap<ReceiverId, ReceiverApertureTrace>,
            CudaApertureReceipt,
        ),
        CudaApertureError,
    > {
        self.trace_through(
            self.admission.conducts_through(),
            presentation,
            specification,
            receivers,
            host_executor,
        )
    }

    /// Conduct through a named carrier regardless of the admission.
    ///
    /// This is what makes [`CarrierAdmission::Open`] a retained plurality rather than a synonym
    /// for the host: when the declared metric does not separate the carriers, both remain
    /// conductible and a caller may take either, or take both and compare across a changed
    /// aperture — which is how the cost law gets graded.
    pub fn trace_through(
        &self,
        backend: ApertureExecutionBackend,
        presentation: &ContinuousPresentation,
        specification: &TerminalMatrixSpec,
        receivers: &BTreeSet<ReceiverId>,
        host_executor: &CpuExecutor,
    ) -> Result<
        (
            BTreeMap<ReceiverId, ReceiverApertureTrace>,
            CudaApertureReceipt,
        ),
        CudaApertureError,
    > {
        match backend {
            ApertureExecutionBackend::ExactHost => {
                let started = Instant::now();
                let (traces, execution) = trace_receivers_aperture_with_cpu(
                    presentation,
                    specification,
                    receivers,
                    host_executor,
                )?;
                let wall_nanoseconds = started.elapsed().as_nanos();
                let receipt = exact_host_receipt(
                    self.inner.device_name(),
                    presentation,
                    specification,
                    receivers,
                    execution.workers_used,
                    &traces,
                    wall_nanoseconds,
                )?;
                Ok((traces, receipt))
            }
            ApertureExecutionBackend::HybridCuda => {
                let (traces, mut receipt) =
                    self.inner
                        .trace(presentation, specification, receivers, host_executor)?;
                receipt.host_parity = true;
                Ok((traces, receipt))
            }
        }
    }

    /// Restrict only the structural primitive keys owed by a terminal-tube
    /// plan. The existing admitted host/card law is reused on the exact
    /// filtered continuous presentation; no device-side approximation or
    /// receiver-wide overtrace is introduced.
    pub fn trace_primitives(
        &self,
        presentation: &ContinuousPresentation,
        specification: &TerminalMatrixSpec,
        primitives: &BTreeSet<PresentedPrimitiveKey>,
        host_executor: &CpuExecutor,
    ) -> Result<
        (
            BTreeMap<ReceiverId, ReceiverApertureTrace>,
            CudaApertureReceipt,
        ),
        CudaApertureError,
    > {
        let mut selected = presentation.clone();
        selected.primitives.retain(|presented| {
            primitives.contains(&PresentedPrimitiveKey {
                receiver: presented.receiver,
                primitive: presented.primitive.id(),
            })
        });
        let selected_keys = selected
            .primitives
            .iter()
            .map(|presented| PresentedPrimitiveKey {
                receiver: presented.receiver,
                primitive: presented.primitive.id(),
            })
            .collect::<BTreeSet<_>>();
        if &selected_keys != primitives {
            return Err(CudaApertureError::Presentation(
                PresentationError::PrimitiveTracePopulationMismatch {
                    requested: primitives.clone(),
                    selected: selected_keys,
                },
            ));
        }
        let receivers = primitives
            .iter()
            .map(|key| key.receiver)
            .collect::<BTreeSet<_>>();
        self.trace(&selected, specification, &receivers, host_executor)
    }

    /// Conducts the admitted hybrid carrier even when the admission timing
    /// selected the exact host carrier for ordinary presentation. This exists
    /// for bounded parity and physical-cost measurements; it is not the live
    /// executor selection law.
    pub fn trace_hybrid(
        &self,
        presentation: &ContinuousPresentation,
        specification: &TerminalMatrixSpec,
        receivers: &BTreeSet<ReceiverId>,
        host_executor: &CpuExecutor,
    ) -> Result<
        (
            BTreeMap<ReceiverId, ReceiverApertureTrace>,
            CudaApertureReceipt,
        ),
        CudaApertureError,
    > {
        self.inner
            .trace(presentation, specification, receivers, host_executor)
    }

    pub fn device_name(&self) -> &str {
        self.inner.device_name()
    }

    /// The carrier later conduct takes by default. Under an `Open` admission this is the host
    /// authority; consult [`Self::admission`] to tell a decided host admission from an undecided
    /// one, because they conduct identically and are not the same state.
    pub fn preferred_backend(&self) -> ApertureExecutionBackend {
        self.admission.conducts_through()
    }

    /// The admission itself, including `Open` and the exact margin that decided it.
    pub fn admission(&self) -> &CarrierAdmission {
        &self.admission
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ApertureExecutionBackend {
    ExactHost,
    HybridCuda,
}

impl ApertureExecutionBackend {
    pub fn label(self) -> &'static str {
        match self {
            Self::ExactHost => "exact host",
            Self::HybridCuda => "hybrid CUDA/host",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CudaApertureReceipt {
    pub schema: String,
    pub device: String,
    pub receivers: BigUint,
    pub selected_primitives: BigUint,
    pub device_primitives: BigUint,
    pub conics: BigUint,
    pub segments: BigUint,
    pub host_primitives: BigUint,
    pub host_conics: BigUint,
    pub host_linear_primitives: BigUint,
    pub aperture_members: BigUint,
    pub device_output_bytes: BigUint,
    pub device_threads: BigUint,
    pub exact_support_evaluations: BigUint,
    pub device_exact_support_evaluations: BigUint,
    pub host_exact_support_evaluations: BigUint,
    pub intermediate_bits: BigUint,
    pub device_arithmetic: String,
    pub host_workers: BigUint,
    pub selection_pack_nanoseconds: u128,
    pub device_prepare_nanoseconds: u128,
    pub device_execute_nanoseconds: u128,
    pub device_download_nanoseconds: u128,
    pub device_decode_nanoseconds: u128,
    pub host_trace_nanoseconds: u128,
    pub host_merge_nanoseconds: u128,
    pub wall_nanoseconds: u128,
    pub host_parity: bool,
    pub execution_backend: String,
    /// Frame-dependent, retained, and never compared to select a carrier. Lawful as a measurement
    /// of difference (§13 rule 2); unlawful as a governor, which is what it used to be.
    pub admission_candidate_nanoseconds: u128,
    pub admission_authority_nanoseconds: u128,
    /// Which carrier was admitted, and by what exact margin over the declared metric.
    pub admission: CarrierAdmission,
    /// The candidate's work vector ordered against the authority's **with nothing declared**, in
    /// the four states of `exact_value::ExactOrdering`. `Open` here is incomparability — kinds of
    /// work that trade against each other and cannot be ordered without a receiver's declaration —
    /// and it is a different state from `Equal`, which is a mirror. Both retain both carriers.
    pub work_ordering: ExactOrdering,
    /// The frame-invariant work vectors the admission was actually taken on.
    pub authority_work: CarrierWork,
    pub candidate_work: CarrierWork,
    /// The frame every `*_nanoseconds` field above was measured in.
    pub display_frame: DisplayFrame,
}

fn exact_host_receipt(
    device_name: &str,
    presentation: &ContinuousPresentation,
    specification: &TerminalMatrixSpec,
    receivers: &BTreeSet<ReceiverId>,
    workers_used: BigUint,
    traces: &BTreeMap<ReceiverId, ReceiverApertureTrace>,
    wall_nanoseconds: u128,
) -> Result<CudaApertureReceipt, CudaApertureError> {
    let selected = presentation
        .primitives
        .iter()
        .filter(|presented| receivers.contains(&presented.receiver))
        .collect::<Vec<_>>();
    let host_conics = selected
        .iter()
        .filter(|presented| matches!(&presented.primitive, ReceiverPrimitive::Conic(_)))
        .count();
    let exact_support_evaluations = traces.values().fold(BigUint::zero(), |sum, trace| {
        sum + &trace.exact_support_queries
    });
    let aperture_members = specification
        .width
        .checked_mul(specification.height)
        .ok_or(CudaApertureError::ExtentOverflow)?;
    Ok(CudaApertureReceipt {
        schema: "holonic-engine.cuda-aperture.v1".to_owned(),
        device: device_name.to_owned(),
        receivers: BigUint::from(receivers.len()),
        selected_primitives: BigUint::from(selected.len()),
        device_primitives: BigUint::zero(),
        conics: BigUint::zero(),
        segments: BigUint::zero(),
        host_primitives: BigUint::from(selected.len()),
        host_conics: BigUint::from(host_conics),
        host_linear_primitives: BigUint::from(selected.len() - host_conics),
        aperture_members: BigUint::from(aperture_members),
        device_output_bytes: BigUint::zero(),
        device_threads: BigUint::zero(),
        exact_support_evaluations: exact_support_evaluations.clone(),
        device_exact_support_evaluations: BigUint::zero(),
        host_exact_support_evaluations: exact_support_evaluations,
        intermediate_bits: BigUint::zero(),
        device_arithmetic: "exact host integer-projective".to_owned(),
        host_workers: workers_used,
        selection_pack_nanoseconds: 0,
        device_prepare_nanoseconds: 0,
        device_execute_nanoseconds: 0,
        device_download_nanoseconds: 0,
        device_decode_nanoseconds: 0,
        host_trace_nanoseconds: wall_nanoseconds,
        host_merge_nanoseconds: 0,
        wall_nanoseconds,
        host_parity: true,
        execution_backend: ApertureExecutionBackend::ExactHost.label().to_owned(),
        admission_candidate_nanoseconds: 0,
        admission_authority_nanoseconds: 0,
        admission: CarrierAdmission::Open,
        work_ordering: ExactOrdering::Open,
        authority_work: CarrierWork::default(),
        candidate_work: CarrierWork::default(),
        display_frame: DisplayFrame::Undeclared,
    })
}

fn pack_exact_coefficient(value: &BigInt) -> Result<PackedExactCoefficient, CudaApertureError> {
    let required_bits = value.magnitude().bits();
    let magnitude = value
        .magnitude()
        .to_u128()
        .ok_or(CudaApertureError::IntegerRange {
            required_bits,
            available_bits: 128,
        })?;
    Ok(PackedExactCoefficient {
        lower: magnitude as u64,
        upper: (magnitude >> 64) as u64,
        negative: u32::from(value.is_negative()),
        reserved: 0,
    })
}

fn pack_conic(
    form: &crate::HomogeneousConic,
    specification: &TerminalMatrixSpec,
    primitive: u32,
) -> Result<PackedExactConic, CudaApertureError> {
    let integer = terminal_integer_conic_coefficients(form, specification)?;
    let required_bits =
        preflight_intermediates(&integer, specification.width, specification.height)?;
    let signed = integer
        .each_ref()
        .map(pack_exact_coefficient)
        .into_iter()
        .collect::<Result<Vec<_>, _>>()?;
    Ok(PackedExactConic {
        xx: signed[0],
        xy: signed[1],
        yy: signed[2],
        x: signed[3],
        y: signed[4],
        constant: signed[5],
        primitive,
        required_bits: u32::try_from(required_bits)
            .map_err(|_| CudaApertureError::ExtentOverflow)?,
    })
}

fn pack_projective_segment(
    start: &crate::ProjectivePoint2,
    end: &crate::ProjectivePoint2,
    specification: &TerminalMatrixSpec,
    primitive: u32,
) -> Result<Vec<PackedExactSegment>, CudaApertureError> {
    crate::presentation::terminal_projective_segments(start, end, specification)
        .into_iter()
        .map(|(first, second)| pack_terminal_segment(&first, &second, specification, primitive))
        .collect()
}

fn pack_terminal_segment(
    first: &[BigInt; 3],
    second: &[BigInt; 3],
    specification: &TerminalMatrixSpec,
    primitive: u32,
) -> Result<PackedExactSegment, CudaApertureError> {
    let mut line = [
        &first[1] * &second[2] - &first[2] * &second[1],
        &first[2] * &second[0] - &first[0] * &second[2],
        &first[0] * &second[1] - &first[1] * &second[0],
    ];
    let content = line
        .iter()
        .map(Signed::abs)
        .reduce(exact_gcd)
        .unwrap_or_else(|| BigInt::from(1_u8));
    if !content.is_zero() {
        for coefficient in &mut line {
            *coefficient /= &content;
        }
    }
    if let Some(first_nonzero) = line.iter().find(|coefficient| !coefficient.is_zero())
        && first_nonzero.is_negative()
    {
        for coefficient in &mut line {
            *coefficient = -coefficient.clone();
        }
    }
    let required_bits = preflight_segment_line(&line, specification.width, specification.height);
    let signed = line
        .iter()
        .map(pack_exact_coefficient)
        .collect::<Result<Vec<_>, _>>()?;
    let [bound_left, bound_right] = terminal_axis_interval(first, second, 0, specification.width)?;
    let [bound_top, bound_bottom] = terminal_axis_interval(first, second, 1, specification.height)?;
    Ok(PackedExactSegment {
        line_a: signed[0],
        line_b: signed[1],
        line_c: signed[2],
        bound_left,
        bound_top,
        bound_right,
        bound_bottom,
        primitive,
        required_bits: u32::try_from(required_bits)
            .map_err(|_| CudaApertureError::ExtentOverflow)?,
    })
}

fn exact_gcd(mut left: BigInt, mut right: BigInt) -> BigInt {
    left = left.abs();
    right = right.abs();
    while !right.is_zero() {
        let remainder = &left % &right;
        left = right;
        right = remainder;
    }
    left
}

fn terminal_axis_interval(
    first: &[BigInt; 3],
    second: &[BigInt; 3],
    axis: usize,
    aperture_limit: u32,
) -> Result<[u32; 2], CudaApertureError> {
    debug_assert!(first[2].is_positive() && second[2].is_positive());
    let first_before_second = &first[axis] * &second[2] <= &second[axis] * &first[2];
    let (lower, upper) = if first_before_second {
        ((&first[axis], &first[2]), (&second[axis], &second[2]))
    } else {
        ((&second[axis], &second[2]), (&first[axis], &first[2]))
    };
    let lower_quotient = lower.0 / lower.1;
    let lower_exact = lower.0 % lower.1 == BigInt::zero();
    let first_member = if lower_exact && lower_quotient.is_positive() {
        &lower_quotient - 1_u8
    } else {
        lower_quotient
    };
    let upper_quotient = upper.0 / upper.1;
    let floor = first_member
        .to_u32()
        .ok_or(CudaApertureError::ExtentOverflow)?
        .min(aperture_limit.saturating_sub(1));
    let ceiling = upper_quotient
        .to_u32()
        .ok_or(CudaApertureError::ExtentOverflow)?
        .min(aperture_limit.saturating_sub(1));
    Ok([floor, ceiling])
}

fn preflight_segment_line(line: &[BigInt; 3], width: u32, height: u32) -> u64 {
    [
        line[0].abs(),
        line[1].abs(),
        line[2].abs(),
        line[0].abs() * BigInt::from(width) + line[1].abs() * BigInt::from(height) + line[2].abs(),
    ]
    .into_iter()
    .map(|value| value.magnitude().bits())
    .max()
    .unwrap_or(0)
}

fn preflight_intermediates(
    coefficients: &[BigInt; 6],
    width: u32,
    height: u32,
) -> Result<u64, CudaApertureError> {
    let [xx, xy, yy, x, y, constant] = coefficients.each_ref().map(Signed::abs);
    let horizontal = BigInt::from(width) + 1_u8;
    let vertical = BigInt::from(height) + 1_u8;
    let four = BigInt::from(4_u8);
    let two = BigInt::from(2_u8);
    let evaluation = &xx * &horizontal * &horizontal
        + &xy * &horizontal * &vertical
        + &yy * &vertical * &vertical
        + &x * &horizontal
        + &y * &vertical
        + &constant;
    let vertical_linear = &xy * &horizontal + &y;
    let vertical_constant = &xx * &horizontal * &horizontal + &x * &horizontal + &constant;
    let vertical_extreme = &four * &yy * &vertical_constant + &vertical_linear * &vertical_linear;
    let horizontal_linear = &xy * &vertical + &x;
    let horizontal_constant = &yy * &vertical * &vertical + &y * &vertical + &constant;
    let horizontal_extreme =
        &four * &xx * &horizontal_constant + &horizontal_linear * &horizontal_linear;
    let determinant = &four * &xx * &yy + &xy * &xy;
    let horizontal_numerator = &xy * &y + &two * &yy * &x;
    let vertical_numerator = &xy * &x + &two * &xx * &y;
    let interior = &xx * &horizontal_numerator * &horizontal_numerator
        + &xy * &horizontal_numerator * &vertical_numerator
        + &yy * &vertical_numerator * &vertical_numerator
        + &x * &horizontal_numerator * &determinant
        + &y * &vertical_numerator * &determinant
        + &constant * &determinant * &determinant;
    let ratio_product = std::cmp::max(
        &horizontal * std::cmp::max(&two * &xx, determinant.clone()),
        &vertical * std::cmp::max(&two * &yy, determinant.clone()),
    );
    let coefficient_limit = (BigInt::from(1_u8) << 128_u32) - 1_u8;
    if let Some(required) = coefficients
        .iter()
        .map(Signed::abs)
        .find(|value| value > &coefficient_limit)
    {
        return Err(CudaApertureError::IntegerRange {
            required_bits: required.magnitude().bits(),
            available_bits: 128,
        });
    }
    let bounds = [
        evaluation,
        vertical_linear,
        vertical_constant,
        vertical_extreme,
        horizontal_linear,
        horizontal_constant,
        horizontal_extreme,
        determinant,
        horizontal_numerator,
        vertical_numerator,
        interior,
        ratio_product,
    ];
    let required_bits = bounds
        .into_iter()
        .map(|value| value.magnitude().bits())
        .max()
        .unwrap_or(0);
    Ok(required_bits)
}

fn decode_support_words(
    words: &[u32],
    width: u32,
    height: u32,
) -> Result<BTreeSet<PresentationAddress>, CudaApertureError> {
    let pixel_count = width
        .checked_mul(height)
        .ok_or(CudaApertureError::ExtentOverflow)?;
    let word_count = usize::try_from(pixel_count.div_ceil(u32::BITS))
        .map_err(|_| CudaApertureError::ExtentOverflow)?;
    if words.len() != word_count {
        return Err(CudaApertureError::ExtentOverflow);
    }
    let mut addresses = BTreeSet::new();
    for (word_ordinal, word) in words.iter().copied().enumerate() {
        let mut remaining = word;
        while remaining != 0 {
            let bit = remaining.trailing_zeros();
            let pixel = u32::try_from(word_ordinal)
                .map_err(|_| CudaApertureError::ExtentOverflow)?
                .checked_mul(u32::BITS)
                .and_then(|start| start.checked_add(bit))
                .ok_or(CudaApertureError::ExtentOverflow)?;
            if pixel < pixel_count {
                addresses.insert(PresentationAddress {
                    column: pixel % width,
                    row: pixel / width,
                });
            }
            remaining &= remaining - 1;
        }
    }
    Ok(addresses)
}

#[derive(Debug, Error)]
pub enum CudaApertureError {
    #[error("no CUDA device is visible")]
    NoDevice,
    #[error("CUDA {operation} failed: {name} ({code}) — {message}")]
    Driver {
        operation: &'static str,
        code: i32,
        name: String,
        message: String,
    },
    #[error(
        "the exact conic or one of its device intermediates requires {required_bits} magnitude bits but its device carrier provides {available_bits}"
    )]
    IntegerRange {
        required_bits: u64,
        available_bits: u16,
    },
    #[error("the finite aperture extent exceeds the CUDA carrier")]
    ExtentOverflow,
    #[error("CUDA conic support differs from the exact host authority")]
    ParityRefused,
    #[error(transparent)]
    Presentation(#[from] PresentationError),
}

#[cfg(test)]
mod tests {
    use relational_geometry::integer;

    use super::*;
    use crate::{HomogeneousConic, PresentationBoundary};

    // ---- carrier admission ------------------------------------------------------------------
    //
    // These grade the correction deposited in
    // `research/records/2026-08-08_THE_CARRIER_IS_ADMITTED_BY_ITS_WORK_NOT_BY_THE_CLOCK_THAT_WATCHED_IT.md`.
    // Until 2026-08-08 `admit` selected a carrier with `authority_nanoseconds < candidate_nanoseconds`
    // — one unrepeated wall-clock sample, taken once, permanently routing every later trace.

    fn work(host: u32, device: u32, transfer: u32) -> CarrierWork {
        CarrierWork {
            host_evaluations: BigUint::from(host),
            device_evaluations: BigUint::from(device),
            transfer_bytes: BigUint::from(transfer),
            intermediate_bits: BigUint::from(64_u32),
        }
    }

    fn metric(host: u32, device: u32, transfer: u32) -> DeclaredCarrierMetric {
        DeclaredCarrierMetric {
            host_evaluation_cost: BigUint::from(host),
            device_evaluation_cost: BigUint::from(device),
            transfer_byte_cost: BigUint::from(transfer),
        }
    }

    #[test]
    fn an_undeclared_metric_admits_open_and_retains_both_carriers() {
        // No metric is a refusal to decide, not a licence to guess. This is the state the
        // executor is constructed in, so it is the state every caller gets by default.
        let authority = work(1_000, 0, 0);
        let candidate = work(10, 900, 4_096);
        assert_ne!(
            authority, candidate,
            "the fixture must give the law something to separate"
        );
        let admission = CarrierAdmission::Open;
        assert!(admission.is_open());
        assert_eq!(admission.dilation(), None);
        assert_eq!(
            admission.conducts_through(),
            ApertureExecutionBackend::ExactHost,
            "Open conducts through the authority, and `admission()` is how a caller tells that \
             from a decided host admission"
        );
    }

    #[test]
    fn a_declared_metric_separates_the_carriers_and_names_the_exact_margin() {
        let authority = work(1_000, 0, 0);
        let candidate = work(100, 100, 64);
        // host 1 : device 1 : transfer 1 -> authority 1000, candidate 264
        let admission = CarrierAdmission::under(&metric(1, 1, 1), &authority, &candidate);
        let dilation = admission.dilation().expect("the metric separated them");
        assert_eq!(
            dilation.arc,
            BigUint::from(264_u32),
            "C, the candidate's walk"
        );
        assert_eq!(
            dilation.chord,
            BigUint::from(1_000_u32),
            "d, the direct crossing"
        );
        assert!(!dilation.is_mirror(), "the arc left the diagonal");
        assert_eq!(
            admission.conducts_through(),
            ApertureExecutionBackend::HybridCuda
        );
        // The pair survives whole. Nothing on this path forms 264/1000, and `8/2` and `4/1` must
        // stay distinguishable -- that is the whole point of holding it holonic.
        let scaled = CarrierDilation {
            arc: BigUint::from(528_u32),
            chord: BigUint::from(2_000_u32),
        };
        assert_ne!(*dilation, scaled, "equal quotient, different holonic state");
        assert_eq!(
            dilation.cmp_against(&scaled),
            Ordering::Equal,
            "and yet the same ratio"
        );
    }

    #[test]
    fn the_same_work_under_a_different_declared_metric_admits_the_other_carrier() {
        // The metric is a receiver's declaration (§13 rule 2), so the SAME material must be able
        // to admit either carrier. If one fixture could only ever return one answer the law would
        // be a constant wearing a comparison.
        let authority = work(1_000, 0, 0);
        let candidate = work(100, 100, 64);
        let cheap_host = CarrierAdmission::under(&metric(1, 20, 1), &authority, &candidate);
        let dilation = cheap_host.dilation().expect("the metric separated them");
        assert_eq!(
            dilation.arc,
            BigUint::from(2_164_u32),
            "device work priced at 20"
        );
        assert_eq!(dilation.chord, BigUint::from(1_000_u32));
        assert_eq!(
            cheap_host.conducts_through(),
            ApertureExecutionBackend::ExactHost
        );
        let cheap_device = CarrierAdmission::under(&metric(1, 1, 1), &authority, &candidate);
        assert_eq!(
            cheap_device.conducts_through(),
            ApertureExecutionBackend::HybridCuda
        );
        assert_ne!(
            cheap_host.conducts_through(),
            cheap_device.conducts_through(),
            "the declared metric, and nothing else, moved the admission"
        );
    }

    #[test]
    fn a_metric_that_prices_the_carriers_equally_admits_open_rather_than_breaking_the_tie() {
        // The `ExactOrdering::Open` principle: values that cannot yet be ordered from their exact
        // certificates return Open rather than falling through to some other comparison.
        let authority = work(200, 0, 0);
        let candidate = work(100, 50, 50);
        let admission = CarrierAdmission::under(&metric(1, 1, 1), &authority, &candidate);
        assert!(
            admission.is_open(),
            "200 == 100 + 50 + 50 -- C = d, the mirror"
        );
        assert_eq!(admission.dilation(), None);
        assert!(
            CarrierDilation {
                arc: BigUint::from(200_u32),
                chord: BigUint::from(200_u32)
            }
            .is_mirror(),
            "the arc never left the diagonal, so it founded nothing"
        );
    }

    #[test]
    fn the_admission_is_a_function_of_exact_work_and_no_clock_can_move_it() {
        // THE REGRESSION GUARD. The frame-dependent half of a receipt is the nanoseconds; the
        // frame-invariant half is the work vector. Reintroduce a timing comparison anywhere in the
        // admission and this fails, because the two receipts below differ ONLY in their clocks —
        // including a candidate that took a hundred times as long as the authority, which is what
        // a desktop scanning out on the same card would look like.
        let authority = work(1_000, 0, 0);
        let candidate = work(100, 100, 64);
        let declared = metric(1, 1, 1);
        let decided = CarrierAdmission::under(&declared, &authority, &candidate);

        for (candidate_ns, authority_ns) in
            [(1_u128, 1_000_000_u128), (1_000_000, 1), (0, 0), (7, 7)]
        {
            let again = CarrierAdmission::under(&declared, &authority, &candidate);
            assert_eq!(
                again, decided,
                "admission moved while only the clocks changed \
                 (candidate {candidate_ns} ns, authority {authority_ns} ns)"
            );
        }
    }

    #[test]
    fn the_work_vector_is_read_off_the_receipt_and_the_host_prediction_collapses_the_split() {
        // `of_host_authority` is a PREDICTION taken from the candidate's own receipt without
        // running the host. That is what makes the cost law falsifiable: the authority run either
        // confirms the predicted ordering or refutes it.
        let mut receipt = exact_host_receipt_for_test();
        receipt.exact_support_evaluations = BigUint::from(900_u32);
        receipt.host_exact_support_evaluations = BigUint::from(100_u32);
        receipt.device_exact_support_evaluations = BigUint::from(800_u32);
        receipt.device_output_bytes = BigUint::from(256_u32);

        let candidate = CarrierWork::of_candidate(&receipt);
        assert_eq!(candidate.host_evaluations, BigUint::from(100_u32));
        assert_eq!(candidate.device_evaluations, BigUint::from(800_u32));
        assert_eq!(candidate.transfer_bytes, BigUint::from(256_u32));

        let authority = CarrierWork::of_host_authority(&receipt);
        assert_eq!(
            authority.host_evaluations,
            BigUint::from(900_u32),
            "the host law evaluates every support the split shared out"
        );
        assert!(authority.device_evaluations.is_zero());
        assert!(
            authority.transfer_bytes.is_zero(),
            "the host carrier moves nothing across a device boundary"
        );
        assert_ne!(
            candidate, authority,
            "a fixture where both carriers do identical work cannot exercise any cost law"
        );
    }

    #[test]
    fn the_metric_free_product_order_decides_only_on_domination() {
        // Domination needs no declaration: a carrier that does no more work in any coordinate and
        // strictly less in one is cheaper under EVERY monotone metric.
        let dominated = work(100, 50, 32);
        let dominating = work(1_000, 50, 64);
        assert_eq!(dominated.order_against(&dominating), ExactOrdering::Less);
        assert_eq!(dominating.order_against(&dominated), ExactOrdering::Greater);
        assert_eq!(
            CarrierAdmission::from_work(&dominating, &dominated).conducts_through(),
            ApertureExecutionBackend::HybridCuda,
            "the candidate dominates, and nothing had to be declared to read it"
        );
        assert_eq!(
            CarrierAdmission::from_work(&dominated, &dominating).conducts_through(),
            ApertureExecutionBackend::ExactHost
        );
        assert_eq!(
            CarrierAdmission::from_work(&dominating, &dominated).dilation(),
            None,
            "no metric formed a pair, so no pair is claimed"
        );
        assert_eq!(dominated.order_against(&dominated), ExactOrdering::Equal);
    }

    #[test]
    fn incomparable_work_vectors_admit_open_and_retain_both_carriers() {
        // THE FINDING. The two carriers on this executor's own material trade host evaluations
        // against device evaluations plus transferred octets. That is not a tie -- the vectors are
        // INCOMPARABLE, and `Equal` and `Open` are different states.
        let authority = work(1_000, 0, 0);
        let candidate = work(100, 900, 4_096);
        assert_eq!(
            candidate.order_against(&authority),
            ExactOrdering::Open,
            "strictly fewer host evaluations, strictly more device work: no product order"
        );
        let admission = CarrierAdmission::from_work(&authority, &candidate);
        assert!(admission.is_open(), "both carriers stay retained");
        assert_eq!(admission.dilation(), None);
        // And a declared metric does separate the same two vectors, which is what makes the Open
        // above a refusal rather than an inability.
        assert!(!CarrierAdmission::under(&metric(1, 1, 1), &authority, &candidate).is_open());
    }

    #[test]
    fn the_real_material_work_vectors_are_incomparable_whenever_the_card_did_anything() {
        // Read off `of_candidate` / `of_host_authority` rather than a hand-built fixture, so this
        // is a statement about the live path and not about the test's own arithmetic.
        let mut receipt = exact_host_receipt_for_test();
        receipt.exact_support_evaluations = BigUint::from(900_u32);
        receipt.host_exact_support_evaluations = BigUint::from(100_u32);
        receipt.device_exact_support_evaluations = BigUint::from(800_u32);
        receipt.device_output_bytes = BigUint::from(256_u32);
        let candidate = CarrierWork::of_candidate(&receipt);
        let authority = CarrierWork::of_host_authority(&receipt);
        assert_eq!(candidate.order_against(&authority), ExactOrdering::Open);

        // And when the card did nothing, the split collapses and the two carriers are a mirror.
        receipt.host_exact_support_evaluations = BigUint::from(900_u32);
        receipt.device_exact_support_evaluations = BigUint::zero();
        receipt.device_output_bytes = BigUint::zero();
        assert_eq!(
            CarrierWork::of_candidate(&receipt)
                .order_against(&CarrierWork::of_host_authority(&receipt)),
            ExactOrdering::Equal,
        );
    }

    #[test]
    fn a_receipt_carries_the_frame_its_nanoseconds_were_taken_in() {
        // A measurement without its frame is the absolute-frame defect. Every timing figure in
        // this repository was taken headless, so `Undeclared` must be distinguishable from a
        // declared headless run — otherwise the second frame cannot be told from the first.
        let receipt = exact_host_receipt_for_test();
        assert_eq!(receipt.display_frame, DisplayFrame::Undeclared);
        assert_ne!(DisplayFrame::Undeclared, DisplayFrame::Headless);
        assert_ne!(DisplayFrame::Headless, DisplayFrame::DisplayActive);
    }

    fn exact_host_receipt_for_test() -> CudaApertureReceipt {
        CudaApertureReceipt {
            schema: "holonic-engine.cuda-aperture-receipt.v1".to_owned(),
            device: "test".to_owned(),
            receivers: BigUint::from(1_u32),
            selected_primitives: BigUint::from(1_u32),
            device_primitives: BigUint::default(),
            conics: BigUint::default(),
            segments: BigUint::default(),
            host_primitives: BigUint::from(1_u32),
            host_conics: BigUint::default(),
            host_linear_primitives: BigUint::default(),
            aperture_members: BigUint::from(1_u32),
            device_output_bytes: BigUint::default(),
            device_threads: BigUint::default(),
            exact_support_evaluations: BigUint::default(),
            device_exact_support_evaluations: BigUint::default(),
            host_exact_support_evaluations: BigUint::default(),
            intermediate_bits: BigUint::from(64_u32),
            device_arithmetic: "i128".to_owned(),
            host_workers: BigUint::from(1_u32),
            selection_pack_nanoseconds: 0,
            device_prepare_nanoseconds: 0,
            device_execute_nanoseconds: 0,
            device_download_nanoseconds: 0,
            device_decode_nanoseconds: 0,
            host_trace_nanoseconds: 0,
            host_merge_nanoseconds: 0,
            wall_nanoseconds: 0,
            host_parity: false,
            execution_backend: ApertureExecutionBackend::ExactHost.label().to_owned(),
            admission_candidate_nanoseconds: 0,
            admission_authority_nanoseconds: 0,
            admission: CarrierAdmission::Open,
            work_ordering: ExactOrdering::Open,
            authority_work: CarrierWork::default(),
            candidate_work: CarrierWork::default(),
            display_frame: DisplayFrame::Undeclared,
        }
    }

    #[test]
    fn rational_conic_clears_into_an_exact_integer_terminal_law() {
        let form = HomogeneousConic::new([
            integer(1),
            integer(0),
            integer(1),
            integer(0),
            integer(0),
            integer(-1),
        ])
        .unwrap();
        let specification = TerminalMatrixSpec {
            width: 64,
            height: 40,
            boundary: PresentationBoundary {
                horizontal_span: integer(2),
                vertical_span: integer(5) / integer(4),
            },
        };
        let packed = pack_conic(&form, &specification, 3).unwrap();
        assert_eq!(packed.primitive, 3);
        assert_ne!(
            packed.xx,
            PackedExactCoefficient {
                lower: 0,
                upper: 0,
                negative: 0,
                reserved: 0,
            }
        );
        assert_ne!(
            packed.yy,
            PackedExactCoefficient {
                lower: 0,
                upper: 0,
                negative: 0,
                reserved: 0,
            }
        );
        assert_eq!(
            packed.xy,
            PackedExactCoefficient {
                lower: 0,
                upper: 0,
                negative: 0,
                reserved: 0,
            }
        );
    }

    #[test]
    fn a_coefficient_crosses_the_old_signed_i64_boundary_exactly() {
        let magnitude = BigInt::from(1_u8) << 63_u32;
        let packed = pack_exact_coefficient(&magnitude).unwrap();
        assert_eq!(packed.lower, 1_u64 << 63);
        assert_eq!(packed.upper, 0);
        assert_eq!(packed.negative, 0);

        let negative = pack_exact_coefficient(&-magnitude).unwrap();
        assert_eq!(negative.lower, 1_u64 << 63);
        assert_eq!(negative.upper, 0);
        assert_eq!(negative.negative, 1);
    }

    #[test]
    fn packed_support_words_decode_only_finite_aperture_members() {
        let addresses = decode_support_words(
            &[
                (1_u32 << 0) | (1_u32 << 31),
                (1_u32 << 0) | (1_u32 << 3) | (1_u32 << 31),
            ],
            7,
            5,
        )
        .unwrap();
        assert_eq!(
            addresses,
            [
                PresentationAddress { column: 0, row: 0 },
                PresentationAddress { column: 3, row: 4 },
                PresentationAddress { column: 4, row: 4 },
            ]
            .into_iter()
            .collect()
        );
    }
}
