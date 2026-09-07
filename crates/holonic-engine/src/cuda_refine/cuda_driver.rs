#![cfg_attr(not(target_os = "linux"), allow(dead_code, non_snake_case))]

use std::ffi::{CStr, c_char, c_void};
use std::ptr;

use thiserror::Error;

pub(super) type CuDevice = i32;
pub(super) type CuContext = *mut c_void;
pub(super) type CuModule = *mut c_void;
pub(super) type CuFunction = *mut c_void;
pub(super) type CuStream = *mut c_void;
pub(super) type CuDevicePtr = u64;

#[cfg(target_os = "linux")]
#[link(name = "cuda")]
unsafe extern "C" {
    pub(super) fn cuInit(flags: u32) -> i32;
    pub(super) fn cuDeviceGetCount(count: *mut i32) -> i32;
    pub(super) fn cuDeviceGet(device: *mut CuDevice, ordinal: i32) -> i32;
    pub(super) fn cuDeviceGetName(name: *mut c_char, length: i32, device: CuDevice) -> i32;
    pub(super) fn cuDeviceGetAttribute(value: *mut i32, attribute: i32, device: CuDevice) -> i32;
    pub(super) fn cuFuncGetAttribute(value: *mut i32, attribute: i32, function: CuFunction) -> i32;
    pub(super) fn cuCtxCreate_v2(context: *mut CuContext, flags: u32, device: CuDevice) -> i32;
    pub(super) fn cuCtxSetCurrent(context: CuContext) -> i32;
    pub(super) fn cuCtxDestroy_v2(context: CuContext) -> i32;
    pub(super) fn cuCtxSynchronize() -> i32;
    pub(super) fn cuModuleLoadData(module: *mut CuModule, image: *const c_void) -> i32;
    pub(super) fn cuModuleUnload(module: CuModule) -> i32;
    pub(super) fn cuModuleGetFunction(
        function: *mut CuFunction,
        module: CuModule,
        name: *const c_char,
    ) -> i32;
    pub(super) fn cuMemAlloc_v2(pointer: *mut CuDevicePtr, bytes: usize) -> i32;
    pub(super) fn cuMemFree_v2(pointer: CuDevicePtr) -> i32;
    pub(super) fn cuMemcpyHtoD_v2(
        destination: CuDevicePtr,
        source: *const c_void,
        bytes: usize,
    ) -> i32;
    pub(super) fn cuMemcpyDtoH_v2(
        destination: *mut c_void,
        source: CuDevicePtr,
        bytes: usize,
    ) -> i32;
    pub(super) fn cuMemcpyDtoDAsync_v2(
        destination: CuDevicePtr,
        source: CuDevicePtr,
        bytes: usize,
        stream: CuStream,
    ) -> i32;
    pub(super) fn cuMemsetD8_v2(destination: CuDevicePtr, value: u8, count: usize) -> i32;
    pub(super) fn cuLaunchKernel(
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
    pub(super) fn cuGetErrorName(error: i32, name: *mut *const c_char) -> i32;
    pub(super) fn cuGetErrorString(error: i32, message: *mut *const c_char) -> i32;
}

// Keep this source type-checkable on non-CUDA hosts without exposing a linker dependency.
// Constructors return an explicit unsupported-device error before these shims are reached.
#[cfg(not(target_os = "linux"))]
const CUDA_UNAVAILABLE: i32 = -1;
#[cfg(not(target_os = "linux"))]
pub(super) unsafe extern "C" fn cuInit(_: u32) -> i32 {
    CUDA_UNAVAILABLE
}
#[cfg(not(target_os = "linux"))]
pub(super) unsafe extern "C" fn cuDeviceGetCount(_: *mut i32) -> i32 {
    CUDA_UNAVAILABLE
}
#[cfg(not(target_os = "linux"))]
pub(super) unsafe extern "C" fn cuDeviceGet(_: *mut CuDevice, _: i32) -> i32 {
    CUDA_UNAVAILABLE
}
#[cfg(not(target_os = "linux"))]
pub(super) unsafe extern "C" fn cuDeviceGetName(_: *mut c_char, _: i32, _: CuDevice) -> i32 {
    CUDA_UNAVAILABLE
}
#[cfg(not(target_os = "linux"))]
pub(super) unsafe extern "C" fn cuDeviceGetAttribute(_: *mut i32, _: i32, _: CuDevice) -> i32 {
    CUDA_UNAVAILABLE
}
#[cfg(not(target_os = "linux"))]
pub(super) unsafe extern "C" fn cuFuncGetAttribute(_: *mut i32, _: i32, _: CuFunction) -> i32 {
    CUDA_UNAVAILABLE
}
#[cfg(not(target_os = "linux"))]
pub(super) unsafe extern "C" fn cuCtxCreate_v2(_: *mut CuContext, _: u32, _: CuDevice) -> i32 {
    CUDA_UNAVAILABLE
}
#[cfg(not(target_os = "linux"))]
pub(super) unsafe extern "C" fn cuCtxSetCurrent(_: CuContext) -> i32 {
    CUDA_UNAVAILABLE
}
#[cfg(not(target_os = "linux"))]
pub(super) unsafe extern "C" fn cuCtxDestroy_v2(_: CuContext) -> i32 {
    CUDA_UNAVAILABLE
}
#[cfg(not(target_os = "linux"))]
pub(super) unsafe extern "C" fn cuCtxSynchronize() -> i32 {
    CUDA_UNAVAILABLE
}
#[cfg(not(target_os = "linux"))]
pub(super) unsafe extern "C" fn cuModuleLoadData(_: *mut CuModule, _: *const c_void) -> i32 {
    CUDA_UNAVAILABLE
}
#[cfg(not(target_os = "linux"))]
pub(super) unsafe extern "C" fn cuModuleUnload(_: CuModule) -> i32 {
    CUDA_UNAVAILABLE
}
#[cfg(not(target_os = "linux"))]
pub(super) unsafe extern "C" fn cuModuleGetFunction(
    _: *mut CuFunction,
    _: CuModule,
    _: *const c_char,
) -> i32 {
    CUDA_UNAVAILABLE
}
#[cfg(not(target_os = "linux"))]
pub(super) unsafe extern "C" fn cuMemAlloc_v2(_: *mut CuDevicePtr, _: usize) -> i32 {
    CUDA_UNAVAILABLE
}
#[cfg(not(target_os = "linux"))]
pub(super) unsafe extern "C" fn cuMemFree_v2(_: CuDevicePtr) -> i32 {
    CUDA_UNAVAILABLE
}
#[cfg(not(target_os = "linux"))]
pub(super) unsafe extern "C" fn cuMemcpyHtoD_v2(_: CuDevicePtr, _: *const c_void, _: usize) -> i32 {
    CUDA_UNAVAILABLE
}
#[cfg(not(target_os = "linux"))]
pub(super) unsafe extern "C" fn cuMemcpyDtoH_v2(_: *mut c_void, _: CuDevicePtr, _: usize) -> i32 {
    CUDA_UNAVAILABLE
}
#[cfg(not(target_os = "linux"))]
pub(super) unsafe extern "C" fn cuMemcpyDtoDAsync_v2(
    _: CuDevicePtr,
    _: CuDevicePtr,
    _: usize,
    _: CuStream,
) -> i32 {
    CUDA_UNAVAILABLE
}
#[cfg(not(target_os = "linux"))]
pub(super) unsafe extern "C" fn cuMemsetD8_v2(_: CuDevicePtr, _: u8, _: usize) -> i32 {
    CUDA_UNAVAILABLE
}
#[cfg(not(target_os = "linux"))]
pub(super) unsafe extern "C" fn cuLaunchKernel(
    _: CuFunction,
    _: u32,
    _: u32,
    _: u32,
    _: u32,
    _: u32,
    _: u32,
    _: u32,
    _: CuStream,
    _: *mut *mut c_void,
    _: *mut *mut c_void,
) -> i32 {
    CUDA_UNAVAILABLE
}
#[cfg(not(target_os = "linux"))]
pub(super) unsafe extern "C" fn cuGetErrorName(_: i32, out: *mut *const c_char) -> i32 {
    if !out.is_null() {
        unsafe {
            *out = std::ptr::null();
        }
    }
    CUDA_UNAVAILABLE
}
#[cfg(not(target_os = "linux"))]
pub(super) unsafe extern "C" fn cuGetErrorString(_: i32, out: *mut *const c_char) -> i32 {
    if !out.is_null() {
        unsafe {
            *out = std::ptr::null();
        }
    }
    CUDA_UNAVAILABLE
}

#[derive(Debug, Error)]
pub enum CudaRefineError {
    #[cfg(target_os = "macos")]
    #[error("Metal {operation} returned {code} ({name}): {message}")]
    Metal {
        operation: &'static str,
        code: i32,
        name: String,
        message: String,
    },
    #[error("the CUDA refinement apparatus is unavailable on this target")]
    UnsupportedDevice,
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
    #[error("the oriented complex incidence section is empty, ragged, or exceeds the device wire")]
    ComplexIncidenceShape,
    #[error("the complex coefficient fronts are empty, ragged, or carry a zero scale")]
    ComplexCurrentShape,
    #[error(
        "an exact complex coefficient front cannot be represented by the signed-word/common-denominator apparatus chart"
    )]
    ComplexCurrentOutsideApparatus,
    #[error("the exact complex incidence accumulation exceeds the signed-word apparatus carrier")]
    ComplexIncidenceAccumulationOverflow,
    #[error(
        "the causal-adjoint-pulled incidence, active factor population, and mixed interaction graph do not form one resident Complex-Parametron body"
    )]
    CoupledComplexParametronShape,
    #[error(
        "the coupled Complex-Parametron current cannot enter the exact signed-word/common-denominator apparatus chart"
    )]
    CoupledComplexParametronCurrentOutsideApparatus,
    #[error(
        "an exact mixed finite-Leibniz contribution cannot enter the signed-word/common-denominator apparatus chart"
    )]
    CoupledComplexParametronMixedOutsideApparatus,
    #[error("the coupled Complex-Parametron contraction exceeds the signed-word apparatus carrier")]
    CoupledComplexParametronAccumulationOverflow,
    #[error(
        "the interval potential incidence is empty, ragged, reversed, or exceeds the device wire"
    )]
    IntervalPotentialShape,
    #[error(
        "the interval potential coefficient front cannot enter the signed-word apparatus chart"
    )]
    IntervalPotentialCurrentOutsideApparatus,
    #[error("the interval potential contraction exceeds the signed-word apparatus carrier")]
    IntervalPotentialAccumulationOverflow,
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
    #[error("the optical term gap {term_gap} exceeds its line gap {line_gap}")]
    OpticalIncidenceAperture { term_gap: u64, line_gap: u64 },
    #[error("the material-operation world-tube arrays do not form one exact addressed passage")]
    MaterialOperationPassageShape,
    #[error("the participant causal-front arrays or deed do not form one addressed receiver")]
    ParticipantCausalFrontShape,
    #[error(
        "the affine barycentric support and situated section do not form one resident transport"
    )]
    AffineBarycentricTransportShape,
    #[error(
        "the morphology-derived membrane incidence, capacities, affine cochains, and constitutive current do not form one resident word"
    )]
    MembraneInteriorWordShape,
    #[error(
        "the resident generated-port successor returned {returned_target_sections} sections while the complete apparatus-neutral ecology returned {expected_target_sections}"
    )]
    GeneratedPortEcologyMismatch {
        expected_target_sections: usize,
        returned_target_sections: usize,
    },
    #[error(
        "the resident generated-port successor has the apparatus-neutral target extent but disagrees in its exact boundary, current, scale, weight, or reconstruction fibre"
    )]
    GeneratedPortEcologyContentMismatch,
    #[error(
        "the complete generated-port ecology returned an exact receiver radical across {occurrence_population} addressed occurrences"
    )]
    GeneratedPortReceiverRadical { occurrence_population: usize },
    #[error("the resident receiver-history coordinates do not realize the complete q/U/fibre law")]
    ReceiverHistoryCompressionMismatch,
    #[error("the exact membrane current cannot enter the signed-word resident apparatus chart")]
    MembraneInteriorCurrentOutsideApparatus,
    #[error(
        "the returned-constraint incidence, covector, and native action do not form one dynamic morphology passage"
    )]
    DynamicMorphologyShape,
    #[error(
        "the ragged native words, offsets, and starting occurrences do not form one addressed front"
    )]
    RaggedNativePassageShape,
    #[error(
        "the media candidates, anchors, typed ports, action, and decoder do not form one joint passage"
    )]
    JointMediaPassageShape,
    #[error(
        "the retained context, derivation, media sections, and receiver reduction do not form one production aperture"
    )]
    ProductionApertureShape,
    #[error("the quadratic sections and chart maps do not form one exact resident transport")]
    QuadraticTransportShape,
    #[error(
        "the exact section families, actions, constraints, moduli, and cultivation standing do not form one resident passage"
    )]
    FixedSectionFamilyShape,
    #[error(
        "the native oriented constraint, factor, carrier charts, and sections do not form one resident passage"
    )]
    NativeFixedSectionFamilyShape,
}

pub(super) fn text(
    query: unsafe extern "C" fn(i32, *mut *const c_char) -> i32,
    code: i32,
) -> String {
    let mut out = ptr::null();
    let status = unsafe { query(code, &mut out) };
    if status == super::CUDA_SUCCESS && !out.is_null() {
        unsafe { CStr::from_ptr(out) }
            .to_string_lossy()
            .into_owned()
    } else {
        "<no CUDA driver description>".to_owned()
    }
}

pub(super) fn driver(code: i32, operation: &'static str) -> Result<(), CudaRefineError> {
    if code == super::CUDA_SUCCESS {
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
pub(super) struct Buffer {
    pub(super) pointer: CuDevicePtr,
}

impl Buffer {
    pub(super) fn alloc(bytes: usize) -> Result<Self, CudaRefineError> {
        let mut pointer = 0;
        driver(
            unsafe { cuMemAlloc_v2(&mut pointer, bytes.max(1)) },
            "cuMemAlloc_v2",
        )
        .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
        Ok(Self { pointer })
    }

    pub(super) fn widest_repeated_aperture(
        population: usize,
        bytes_for: impl Fn(usize) -> Option<usize>,
    ) -> Result<(usize, Self), CudaRefineError> {
        const CUDA_ERROR_OUT_OF_MEMORY: i32 = 2;
        if population == 0 || bytes_for(1).is_none() {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }
        let mut lower = 1_usize;
        let mut upper = population;
        let mut widest = 0_usize;
        while lower <= upper {
            let candidate = lower + (upper - lower) / 2;
            let bytes = bytes_for(candidate)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let mut pointer = 0;
            let status = unsafe { cuMemAlloc_v2(&mut pointer, bytes.max(1)) };
            if status == super::CUDA_SUCCESS {
                driver(unsafe { cuMemFree_v2(pointer) }, "cuMemFree_v2")?;
                widest = candidate;
                lower = candidate.saturating_add(1);
            } else if status == CUDA_ERROR_OUT_OF_MEMORY {
                if candidate == 0 {
                    break;
                }
                upper = candidate - 1;
            } else {
                return Err(CudaRefineError::Driver {
                    operation: "cuMemAlloc_v2(aperture probe)",
                    code: status,
                    name: text(cuGetErrorName, status),
                    message: text(cuGetErrorString, status),
                });
            }
        }
        if widest == 0 {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }
        Ok((
            widest,
            Self::alloc(
                bytes_for(widest)
                    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
            )?,
        ))
    }

    pub(super) fn of<T: Copy>(values: &[T]) -> Result<Self, CudaRefineError> {
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

    pub(super) fn read<T: Copy>(&self, into: &mut [T]) -> Result<(), CudaRefineError> {
        let bytes = std::mem::size_of_val(into);
        if bytes > 0 {
            driver(
                unsafe { cuMemcpyDtoH_v2(into.as_mut_ptr().cast(), self.pointer, bytes) },
                "cuMemcpyDtoH_v2",
            )?;
        }
        Ok(())
    }

    pub(super) fn fill(&self, byte: u8, bytes: usize) -> Result<(), CudaRefineError> {
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
