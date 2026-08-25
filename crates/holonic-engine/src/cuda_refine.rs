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

use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};
use relational_geometry::Rat;
use thiserror::Error;

use crate::ExactComplexWaveCurrent;
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
    complex_incidence: CuFunction,
    interval_potential_receiver: CuFunction,
    native_trace: CuFunction,
    native_ragged_trace: CuFunction,
    returned_recurrence: CuFunction,
    dynamic_morphology: CuFunction,
    condensed_recurrence: CuFunction,
    heterogeneous_fusion: CuFunction,
    media_candidate_counts: CuFunction,
    joint_media_transport: CuFunction,
    production_aperture_fronts: CuFunction,
    production_aperture_reduction: CuFunction,
    quadratic_section_transport: CuFunction,
    fixed_section_families: CuFunction,
    native_fixed_section_families: CuFunction,
    fixed_section_family_reduction: CuFunction,
    inference_ecology: CuFunction,
    material_operation_world_tube: CuFunction,
    contact_pairs: CuFunction,
    contact_compare: CuFunction,
    optical_incidence: CuFunction,
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
            let mut complex_incidence = ptr::null_mut();
            let mut interval_potential_receiver = ptr::null_mut();
            let mut native_trace = ptr::null_mut();
            let mut native_ragged_trace = ptr::null_mut();
            let mut returned_recurrence = ptr::null_mut();
            let mut dynamic_morphology = ptr::null_mut();
            let mut condensed_recurrence = ptr::null_mut();
            let mut heterogeneous_fusion = ptr::null_mut();
            let mut media_candidate_counts = ptr::null_mut();
            let mut joint_media_transport = ptr::null_mut();
            let mut production_aperture_fronts = ptr::null_mut();
            let mut production_aperture_reduction = ptr::null_mut();
            let mut quadratic_section_transport = ptr::null_mut();
            let mut fixed_section_families = ptr::null_mut();
            let mut native_fixed_section_families = ptr::null_mut();
            let mut fixed_section_family_reduction = ptr::null_mut();
            let mut inference_ecology = ptr::null_mut();
            let mut material_operation_world_tube = ptr::null_mut();
            let mut contact_pairs = ptr::null_mut();
            let mut contact_compare = ptr::null_mut();
            let mut optical_incidence = ptr::null_mut();
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
                    &mut complex_incidence as *mut CuFunction,
                    c"conduct_complex_incidence",
                    "cuModuleGetFunction(conduct_complex_incidence)",
                ),
                (
                    &mut interval_potential_receiver as *mut CuFunction,
                    c"receive_interval_potential_incidence",
                    "cuModuleGetFunction(receive_interval_potential_incidence)",
                ),
                (
                    &mut native_trace as *mut CuFunction,
                    c"conduct_native_trace",
                    "cuModuleGetFunction(conduct_native_trace)",
                ),
                (
                    &mut native_ragged_trace as *mut CuFunction,
                    c"conduct_native_ragged_trace",
                    "cuModuleGetFunction(conduct_native_ragged_trace)",
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
                    &mut media_candidate_counts as *mut CuFunction,
                    c"derive_media_candidate_counts",
                    "cuModuleGetFunction(derive_media_candidate_counts)",
                ),
                (
                    &mut joint_media_transport as *mut CuFunction,
                    c"conduct_joint_media_transport",
                    "cuModuleGetFunction(conduct_joint_media_transport)",
                ),
                (
                    &mut production_aperture_fronts as *mut CuFunction,
                    c"conduct_production_aperture_fronts",
                    "cuModuleGetFunction(conduct_production_aperture_fronts)",
                ),
                (
                    &mut production_aperture_reduction as *mut CuFunction,
                    c"reduce_production_aperture_fronts",
                    "cuModuleGetFunction(reduce_production_aperture_fronts)",
                ),
                (
                    &mut quadratic_section_transport as *mut CuFunction,
                    c"conduct_quadratic_section_transport",
                    "cuModuleGetFunction(conduct_quadratic_section_transport)",
                ),
                (
                    &mut fixed_section_families as *mut CuFunction,
                    c"conduct_fixed_section_families",
                    "cuModuleGetFunction(conduct_fixed_section_families)",
                ),
                (
                    &mut native_fixed_section_families as *mut CuFunction,
                    c"conduct_native_fixed_section_families",
                    "cuModuleGetFunction(conduct_native_fixed_section_families)",
                ),
                (
                    &mut fixed_section_family_reduction as *mut CuFunction,
                    c"reduce_fixed_section_families",
                    "cuModuleGetFunction(reduce_fixed_section_families)",
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
                (
                    &mut optical_incidence as *mut CuFunction,
                    c"classify_optical_incidence",
                    "cuModuleGetFunction(classify_optical_incidence)",
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
                complex_incidence,
                interval_potential_receiver,
                native_trace,
                native_ragged_trace,
                returned_recurrence,
                dynamic_morphology,
                condensed_recurrence,
                heterogeneous_fusion,
                media_candidate_counts,
                joint_media_transport,
                production_aperture_fronts,
                production_aperture_reduction,
                quadratic_section_transport,
                fixed_section_families,
                native_fixed_section_families,
                fixed_section_family_reduction,
                inference_ecology,
                material_operation_world_tube,
                contact_pairs,
                contact_compare,
                optical_incidence,
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
                complex_incidence,
                interval_potential_receiver,
                native_trace,
                native_ragged_trace,
                returned_recurrence,
                dynamic_morphology,
                condensed_recurrence,
                heterogeneous_fusion,
                media_candidate_counts,
                joint_media_transport,
                production_aperture_fronts,
                production_aperture_reduction,
                quadratic_section_transport,
                fixed_section_families,
                native_fixed_section_families,
                fixed_section_family_reduction,
                inference_ecology,
                material_operation_world_tube,
                contact_pairs,
                contact_compare,
                optical_incidence,
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

/// One native action and ordered word retained on the card across successor occurrences.
///
/// Unlike [`DeviceNativeWord`], this is a continuing apparatus owner rather than the receipt of
/// one call.  The generator table and word cross exactly once at mount.  Every later conduct
/// crosses only its addressed starting population and reads only the terminal population; no
/// invariant transport is re-uploaded between successor occurrences.
pub struct ResidentNativeWord {
    // Device allocations must be released before the context which owns them. Rust drops fields
    // in declaration order, so these precede `card` deliberately.
    generator_table: Buffer,
    word: Buffer,
    card: CudaRefineExecutor,
    states: u32,
    word_length: u32,
    resident_invariant_octets: u64,
    mount_host_ingress_octets: u64,
}

/// One terminal return from an already-resident native word.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResidentNativeWordReturn {
    pub native_end: Vec<u32>,
    pub launches: u64,
    pub synchronizations: u64,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_invariant_octets: u64,
    pub resident_working_octets: u64,
    pub invariant_transport_reuploaded: bool,
}

/// One real incidence section retained on the card while exact complex coefficient currents cross
/// it.  In the Complex Parametron reading, rows are oriented carrier branches, columns are the
/// addressed coefficient nodes, and the two current coordinates retain relative phase before any
/// binary receiver is taken.  The owner is singular and deliberately not `Clone`.
pub struct ResidentComplexIncidence {
    // Released before the context which owns it.
    incidence: Buffer,
    card: CudaRefineExecutor,
    address: String,
    grain: u32,
    branches: u32,
    nodes: u32,
    greatest_row_mass: u128,
    mount_host_ingress_octets: u64,
}

/// One terminal exact complex section returned from the resident incidence map.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentComplexIncidenceReturn {
    pub address: String,
    /// Physical values are these exact coordinates multiplied by `2^-grain`.
    pub grain: u32,
    pub sections: Vec<Vec<ExactComplexWaveCurrent>>,
    pub device: String,
    pub launches: u64,
    pub synchronizations: u64,
    pub block_threads: u32,
    pub mount_host_ingress_octets: u64,
    pub successor_host_ingress_octets: u64,
    pub successor_host_egress_octets: u64,
    pub resident_invariant_octets: u64,
    pub resident_working_octets: u64,
    pub invariant_transport_reuploaded: bool,
    pub cpu_semantic_replay_after_device: bool,
    pub binary_receiver_taken: bool,
}

impl ResidentComplexIncidence {
    /// Mount one exact oriented incidence map. Its extents and row-mass aperture are read from the
    /// material; no hidden width or phase population is authored.
    pub fn mount(
        card: CudaRefineExecutor,
        address: impl Into<String>,
        grain: u32,
        branches: usize,
        nodes: usize,
        incidence: &[i64],
    ) -> Result<Self, CudaRefineError> {
        let expected = branches
            .checked_mul(nodes)
            .ok_or(CudaRefineError::ComplexIncidenceShape)?;
        if branches == 0
            || nodes == 0
            || incidence.len() != expected
            || branches > u32::MAX as usize
            || nodes > u32::MAX as usize
        {
            return Err(CudaRefineError::ComplexIncidenceShape);
        }
        let greatest_row_mass = incidence
            .chunks_exact(nodes)
            .map(|row| {
                row.iter().fold(0u128, |mass, entry| {
                    mass.saturating_add(u128::from(entry.unsigned_abs()))
                })
            })
            .max()
            .unwrap_or(0);
        let mount_host_ingress_octets = u64::try_from(std::mem::size_of_val(incidence))
            .map_err(|_| CudaRefineError::ComplexIncidenceShape)?;
        driver(unsafe { cuCtxSetCurrent(card.context) }, "cuCtxSetCurrent")?;
        let incidence = Buffer::of(incidence)?;
        Ok(Self {
            incidence,
            card,
            address: address.into(),
            grain,
            branches: branches as u32,
            nodes: nodes as u32,
            greatest_row_mass,
            mount_host_ingress_octets,
        })
    }

    pub fn device_name(&self) -> &str {
        self.card.device_name()
    }

    pub fn address(&self) -> &str {
        &self.address
    }

    pub fn grain(&self) -> u32 {
        self.grain
    }

    /// Carry arbitrary exact rational phase pairs through the already-mounted real incidence map.
    /// Each front is rebased to its own common positive denominator at the apparatus mouth and
    /// reconstructed exactly after the terminal read. The card performs both contractions; the
    /// host neither selects a phase nor replays the product.
    pub fn conduct(
        &mut self,
        fronts: &[Vec<ExactComplexWaveCurrent>],
    ) -> Result<ResidentComplexIncidenceReturn, CudaRefineError> {
        let nodes = self.nodes as usize;
        if fronts.is_empty() || fronts.iter().any(|front| front.len() != nodes) {
            return Err(CudaRefineError::ComplexCurrentShape);
        }
        if fronts.len() > u32::MAX as usize {
            return Err(CudaRefineError::ComplexCurrentShape);
        }

        let mut real = Vec::with_capacity(fronts.len() * nodes);
        let mut imaginary = Vec::with_capacity(fronts.len() * nodes);
        let mut denominators = Vec::with_capacity(fronts.len());
        let mut greatest_numerator = 0u128;
        for front in fronts {
            let denominator = common_complex_denominator(front)?;
            for current in front {
                let re = current.real.numer() * (&denominator / current.real.denom());
                let im = current.imaginary.numer() * (&denominator / current.imaginary.denom());
                let re = re
                    .to_i64()
                    .ok_or(CudaRefineError::ComplexCurrentOutsideApparatus)?;
                let im = im
                    .to_i64()
                    .ok_or(CudaRefineError::ComplexCurrentOutsideApparatus)?;
                greatest_numerator = greatest_numerator
                    .max(u128::from(re.unsigned_abs()))
                    .max(u128::from(im.unsigned_abs()));
                real.push(re);
                imaginary.push(im);
            }
            denominators.push(
                denominator
                    .to_u64()
                    .ok_or(CudaRefineError::ComplexCurrentOutsideApparatus)?,
            );
        }
        if self
            .greatest_row_mass
            .checked_mul(greatest_numerator)
            .filter(|bound| *bound <= i64::MAX as u128)
            .is_none()
        {
            return Err(CudaRefineError::ComplexIncidenceAccumulationOverflow);
        }

        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        let coefficient_real = Buffer::of(&real)?;
        let coefficient_imaginary = Buffer::of(&imaginary)?;
        let output_count = fronts
            .len()
            .checked_mul(self.branches as usize)
            .ok_or(CudaRefineError::ComplexIncidenceShape)?;
        let section_real = Buffer::alloc(output_count * std::mem::size_of::<i64>())?;
        let section_imaginary = Buffer::alloc(output_count * std::mem::size_of::<i64>())?;
        if output_count > 0 {
            let grid = self.card.grid_for(output_count as u64)?;
            let mut incidence_pointer = self.incidence.pointer;
            let mut real_pointer = coefficient_real.pointer;
            let mut imaginary_pointer = coefficient_imaginary.pointer;
            let mut section_real_pointer = section_real.pointer;
            let mut section_imaginary_pointer = section_imaginary.pointer;
            let mut branch_count = self.branches;
            let mut node_count = self.nodes;
            let mut front_count = fronts.len() as u32;
            let mut arguments: [*mut c_void; 8] = [
                &mut incidence_pointer as *mut u64 as *mut c_void,
                &mut real_pointer as *mut u64 as *mut c_void,
                &mut imaginary_pointer as *mut u64 as *mut c_void,
                &mut section_real_pointer as *mut u64 as *mut c_void,
                &mut section_imaginary_pointer as *mut u64 as *mut c_void,
                &mut branch_count as *mut u32 as *mut c_void,
                &mut node_count as *mut u32 as *mut c_void,
                &mut front_count as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.card.complex_incidence,
                        grid,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(conduct_complex_incidence)",
            )?;
            driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
            self.card.launches += 1;
        }
        let mut returned_real = vec![0i64; output_count];
        let mut returned_imaginary = vec![0i64; output_count];
        section_real.read(&mut returned_real)?;
        section_imaginary.read(&mut returned_imaginary)?;
        let branches = self.branches as usize;
        let sections = denominators
            .iter()
            .enumerate()
            .map(|(front, denominator)| {
                (0..branches)
                    .map(|branch| {
                        let at = front * branches + branch;
                        ExactComplexWaveCurrent::new(
                            Rat::new(BigInt::from(returned_real[at]), BigInt::from(*denominator)),
                            Rat::new(
                                BigInt::from(returned_imaginary[at]),
                                BigInt::from(*denominator),
                            ),
                        )
                    })
                    .collect()
            })
            .collect();
        let coefficient_octets = std::mem::size_of_val(real.as_slice())
            .checked_add(std::mem::size_of_val(imaginary.as_slice()))
            .and_then(|octets| octets.checked_add(std::mem::size_of_val(denominators.as_slice())))
            .ok_or(CudaRefineError::ComplexIncidenceShape)? as u64;
        let output_octets = output_count
            .checked_mul(2 * std::mem::size_of::<i64>())
            .ok_or(CudaRefineError::ComplexIncidenceShape)? as u64;
        Ok(ResidentComplexIncidenceReturn {
            address: self.address.clone(),
            grain: self.grain,
            sections,
            device: self.card.device_name().to_owned(),
            launches: u64::from(output_count > 0),
            synchronizations: u64::from(output_count > 0),
            block_threads: self.card.block_threads(),
            mount_host_ingress_octets: self.mount_host_ingress_octets,
            successor_host_ingress_octets: coefficient_octets,
            successor_host_egress_octets: output_octets,
            resident_invariant_octets: self.mount_host_ingress_octets,
            resident_working_octets: coefficient_octets + output_octets,
            invariant_transport_reuploaded: false,
            cpu_semantic_replay_after_device: false,
            binary_receiver_taken: false,
        })
    }
}

/// One exact interval-valued potential incidence with its declared receiver-sufficient row cover
/// retained on the card. The complete omitted fibre belongs to the resting causal section; this
/// apparatus owner mounts only the rows through which the declared exterior receiver factors.
pub struct ResidentIntervalPotentialReceiver {
    lower_incidence: Buffer,
    upper_incidence: Buffer,
    row_addresses: Buffer,
    card: CudaRefineExecutor,
    address: String,
    rows: u32,
    nodes: u32,
    greatest_row_mass: u128,
    mount_host_ingress_octets: u64,
}

/// One exact receiver projection from an already-resident interval potential complex.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentIntervalPotentialReturn {
    pub address: String,
    pub selected_native_addresses: Vec<u32>,
    pub selected_lower: Vec<String>,
    pub selected_upper: Vec<String>,
    pub plural_population: Vec<u32>,
    pub device: String,
    pub launches: u64,
    pub synchronizations: u64,
    pub block_threads: u32,
    pub mount_host_ingress_octets: u64,
    pub successor_host_ingress_octets: u64,
    pub successor_host_egress_octets: u64,
    pub resident_invariant_octets: u64,
    pub resident_working_octets: u64,
    pub invariant_transport_reuploaded: bool,
    pub cpu_semantic_replay_after_device: bool,
}

impl ResidentIntervalPotentialReceiver {
    pub fn mount(
        card: CudaRefineExecutor,
        address: impl Into<String>,
        rows: usize,
        nodes: usize,
        row_addresses: &[u32],
        lower_incidence: &[i64],
        upper_incidence: &[i64],
    ) -> Result<Self, CudaRefineError> {
        let expected = rows
            .checked_mul(nodes)
            .ok_or(CudaRefineError::IntervalPotentialShape)?;
        let unique_addresses = row_addresses.iter().copied().collect::<BTreeSet<_>>();
        if rows == 0
            || nodes == 0
            || rows > u32::MAX as usize
            || nodes > u32::MAX as usize
            || row_addresses.len() != rows
            || unique_addresses.len() != rows
            || lower_incidence.len() != expected
            || upper_incidence.len() != expected
            || lower_incidence
                .iter()
                .zip(upper_incidence)
                .any(|(lower, upper)| lower > upper)
        {
            return Err(CudaRefineError::IntervalPotentialShape);
        }
        let greatest_row_mass = lower_incidence
            .chunks_exact(nodes)
            .zip(upper_incidence.chunks_exact(nodes))
            .map(|(lower, upper)| {
                lower.iter().zip(upper).fold(0u128, |mass, (from, until)| {
                    mass.saturating_add(
                        u128::from(from.unsigned_abs()).max(u128::from(until.unsigned_abs())),
                    )
                })
            })
            .max()
            .unwrap_or(0);
        let mount_host_ingress_octets = std::mem::size_of_val(lower_incidence)
            .checked_add(std::mem::size_of_val(upper_incidence))
            .and_then(|octets| octets.checked_add(std::mem::size_of_val(row_addresses)))
            .and_then(|octets| u64::try_from(octets).ok())
            .ok_or(CudaRefineError::IntervalPotentialShape)?;
        driver(unsafe { cuCtxSetCurrent(card.context) }, "cuCtxSetCurrent")?;
        Ok(Self {
            lower_incidence: Buffer::of(lower_incidence)?,
            upper_incidence: Buffer::of(upper_incidence)?,
            row_addresses: Buffer::of(row_addresses)?,
            card,
            address: address.into(),
            rows: rows as u32,
            nodes: nodes as u32,
            greatest_row_mass,
            mount_host_ingress_octets,
        })
    }

    /// Cross exact real coefficient currents and take the declared interval-order receiver on the
    /// card. A plural return remains explicit; this method never lets the host break a tie.
    pub fn conduct(
        &mut self,
        fronts: &[Vec<Rat>],
    ) -> Result<ResidentIntervalPotentialReturn, CudaRefineError> {
        let nodes = self.nodes as usize;
        if fronts.is_empty()
            || fronts.len() > u32::MAX as usize
            || fronts.iter().any(|front| front.len() != nodes)
        {
            return Err(CudaRefineError::IntervalPotentialShape);
        }
        let mut coefficients = Vec::with_capacity(fronts.len() * nodes);
        let mut denominators = Vec::with_capacity(fronts.len());
        let mut greatest_numerator = 0u128;
        for front in fronts {
            let denominator = common_real_denominator(front)?;
            for coefficient in front {
                let numerator = coefficient.numer() * (&denominator / coefficient.denom());
                let numerator = numerator
                    .to_i64()
                    .ok_or(CudaRefineError::IntervalPotentialCurrentOutsideApparatus)?;
                greatest_numerator = greatest_numerator.max(u128::from(numerator.unsigned_abs()));
                coefficients.push(numerator);
            }
            denominators.push(
                denominator
                    .to_u64()
                    .ok_or(CudaRefineError::IntervalPotentialCurrentOutsideApparatus)?,
            );
        }
        if self
            .greatest_row_mass
            .checked_mul(greatest_numerator)
            .filter(|bound| *bound <= i64::MAX as u128)
            .is_none()
        {
            return Err(CudaRefineError::IntervalPotentialAccumulationOverflow);
        }

        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        let coefficient = Buffer::of(&coefficients)?;
        let front_count = fronts.len();
        let selected_address = Buffer::alloc(front_count * std::mem::size_of::<u32>())?;
        let selected_lower = Buffer::alloc(front_count * std::mem::size_of::<i64>())?;
        let selected_upper = Buffer::alloc(front_count * std::mem::size_of::<i64>())?;
        let plural_count = Buffer::alloc(front_count * std::mem::size_of::<u32>())?;
        let mut lower_pointer = self.lower_incidence.pointer;
        let mut upper_pointer = self.upper_incidence.pointer;
        let mut address_pointer = self.row_addresses.pointer;
        let mut coefficient_pointer = coefficient.pointer;
        let mut selected_address_pointer = selected_address.pointer;
        let mut selected_lower_pointer = selected_lower.pointer;
        let mut selected_upper_pointer = selected_upper.pointer;
        let mut plural_pointer = plural_count.pointer;
        let mut rows = self.rows;
        let mut nodes = self.nodes;
        let mut arguments: [*mut c_void; 10] = [
            &mut lower_pointer as *mut u64 as *mut c_void,
            &mut upper_pointer as *mut u64 as *mut c_void,
            &mut address_pointer as *mut u64 as *mut c_void,
            &mut coefficient_pointer as *mut u64 as *mut c_void,
            &mut selected_address_pointer as *mut u64 as *mut c_void,
            &mut selected_lower_pointer as *mut u64 as *mut c_void,
            &mut selected_upper_pointer as *mut u64 as *mut c_void,
            &mut plural_pointer as *mut u64 as *mut c_void,
            &mut rows as *mut u32 as *mut c_void,
            &mut nodes as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.interval_potential_receiver,
                    front_count as u32,
                    1,
                    1,
                    self.card.warp,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(receive_interval_potential_incidence)",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.card.launches += 1;
        let mut returned_address = vec![0u32; front_count];
        let mut returned_lower = vec![0i64; front_count];
        let mut returned_upper = vec![0i64; front_count];
        let mut returned_plural = vec![0u32; front_count];
        selected_address.read(&mut returned_address)?;
        selected_lower.read(&mut returned_lower)?;
        selected_upper.read(&mut returned_upper)?;
        plural_count.read(&mut returned_plural)?;
        if returned_plural.iter().any(|plural| *plural == 0)
            || returned_lower
                .iter()
                .zip(&returned_upper)
                .any(|(lower, upper)| lower > upper)
        {
            return Err(CudaRefineError::IntervalPotentialShape);
        }
        let lower = returned_lower
            .into_iter()
            .zip(&denominators)
            .map(|(numerator, denominator)| {
                Rat::new(BigInt::from(numerator), BigInt::from(*denominator)).to_string()
            })
            .collect();
        let upper = returned_upper
            .into_iter()
            .zip(&denominators)
            .map(|(numerator, denominator)| {
                Rat::new(BigInt::from(numerator), BigInt::from(*denominator)).to_string()
            })
            .collect();
        let ingress = std::mem::size_of_val(coefficients.as_slice()) as u64;
        let egress = front_count
            .checked_mul(2 * std::mem::size_of::<u32>() + 2 * std::mem::size_of::<i64>())
            .ok_or(CudaRefineError::IntervalPotentialShape)? as u64;
        Ok(ResidentIntervalPotentialReturn {
            address: self.address.clone(),
            selected_native_addresses: returned_address,
            selected_lower: lower,
            selected_upper: upper,
            plural_population: returned_plural,
            device: self.card.device_name().to_owned(),
            launches: 1,
            synchronizations: 1,
            block_threads: self.card.warp,
            mount_host_ingress_octets: self.mount_host_ingress_octets,
            successor_host_ingress_octets: ingress,
            successor_host_egress_octets: egress,
            resident_invariant_octets: self.mount_host_ingress_octets,
            resident_working_octets: ingress + egress,
            invariant_transport_reuploaded: false,
            cpu_semantic_replay_after_device: false,
        })
    }
}

fn common_real_denominator(front: &[Rat]) -> Result<BigInt, CudaRefineError> {
    let mut common = BigInt::one();
    for denominator in front.iter().map(Rat::denom) {
        if denominator.is_zero() {
            return Err(CudaRefineError::IntervalPotentialCurrentOutsideApparatus);
        }
        let gcd = integer_gcd(common.clone(), denominator.clone());
        common = (common / gcd) * denominator;
    }
    Ok(common)
}

fn common_complex_denominator(
    front: &[ExactComplexWaveCurrent],
) -> Result<BigInt, CudaRefineError> {
    let mut common = BigInt::one();
    for denominator in front
        .iter()
        .flat_map(|current| [current.real.denom(), current.imaginary.denom()])
    {
        if denominator.is_zero() {
            return Err(CudaRefineError::ComplexCurrentShape);
        }
        let divisor = integer_gcd(common.clone(), denominator.clone());
        common = (common / divisor) * denominator;
    }
    Ok(common.abs())
}

fn integer_gcd(mut left: BigInt, mut right: BigInt) -> BigInt {
    left = left.abs();
    right = right.abs();
    while !right.is_zero() {
        let remainder = left % &right;
        left = right;
        right = remainder;
    }
    if left.is_zero() { BigInt::one() } else { left }
}

impl ResidentNativeWord {
    /// Mount one finite native action and its complete ordered word as continuing device standing.
    pub fn mount(
        card: CudaRefineExecutor,
        states: usize,
        generators: usize,
        generator_table: &[u32],
        word: &[u32],
    ) -> Result<Self, CudaRefineError> {
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
        {
            return Err(CudaRefineError::NativeActionTooWide);
        }
        if let Some(state) = generator_table
            .iter()
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
        driver(unsafe { cuCtxSetCurrent(card.context) }, "cuCtxSetCurrent")?;
        let word_length = word.len();
        let generator_table = Buffer::of(generator_table)?;
        let word = Buffer::of(word)?;
        let resident_invariant_octets = expected
            .checked_mul(std::mem::size_of::<u32>())
            .and_then(|octets| octets.checked_add(word_length * std::mem::size_of::<u32>()))
            .ok_or(CudaRefineError::NativeActionTooWide)?
            as u64;
        Ok(Self {
            generator_table,
            word,
            card,
            states: states as u32,
            word_length: word_length as u32,
            resident_invariant_octets,
            mount_host_ingress_octets: resident_invariant_octets,
        })
    }

    pub fn device_name(&self) -> &str {
        self.card.device_name()
    }

    pub fn block_threads(&self) -> u32 {
        self.card.block_threads()
    }

    pub fn mount_host_ingress_octets(&self) -> u64 {
        self.mount_host_ingress_octets
    }

    pub fn resident_invariant_octets(&self) -> u64 {
        self.resident_invariant_octets
    }

    /// Carry a later addressed population through the already-resident action and word.
    pub fn conduct(
        &mut self,
        native_start: &[u32],
    ) -> Result<ResidentNativeWordReturn, CudaRefineError> {
        if native_start.len() > u32::MAX as usize {
            return Err(CudaRefineError::NativeActionTooWide);
        }
        if let Some(state) = native_start
            .iter()
            .copied()
            .find(|state| *state >= self.states)
        {
            return Err(CudaRefineError::NativeStateOutsidePopulation {
                state,
                states: self.states as usize,
            });
        }

        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        let start = Buffer::of(native_start)?;
        let end = Buffer::alloc(std::mem::size_of_val(native_start))?;
        let count = native_start.len();
        if count > 0 {
            let grid = self.card.grid_for(count as u64)?;
            let mut table_pointer = self.generator_table.pointer;
            let mut word_pointer = self.word.pointer;
            let mut start_pointer = start.pointer;
            let mut end_pointer = end.pointer;
            let mut cell_count = count as u32;
            let mut state_count = self.states;
            let mut word_length = self.word_length;
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
                        self.card.native_word,
                        grid,
                        1,
                        1,
                        self.card.block_x,
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
            self.card.launches += 1;
        }
        let mut native_end = vec![0u32; count];
        if count > 0 {
            end.read(&mut native_end)?;
        }
        let state_octets = std::mem::size_of_val(native_start) as u64;
        Ok(ResidentNativeWordReturn {
            native_end,
            launches: u64::from(count > 0),
            synchronizations: u64::from(count > 0),
            host_ingress_octets: state_octets,
            host_egress_octets: state_octets,
            resident_invariant_octets: self.resident_invariant_octets,
            resident_working_octets: state_octets * 2,
            invariant_transport_reuploaded: false,
        })
    }
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

/// Plural ordered words and their exact ragged traces returned by one resident card front.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceRaggedNativeTrace {
    /// Concatenated traces.  Each interval is selected by `trace_offsets[i..=i + 1]`.
    pub native_trace: Vec<u32>,
    pub trace_offsets: Vec<u32>,
    pub front_count: usize,
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

/// The complete source correspondence multiplicity at each anchor/port cell.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceMediaCandidateCounts {
    /// Anchor-major, port-minor.
    pub candidate_counts: Vec<u32>,
    pub anchors: usize,
    pub ports: usize,
    pub pairs: usize,
    pub launches: u64,
    pub synchronizations: u64,
    pub block_threads: u32,
    pub active_lanes: u32,
    pub semantic_pair_visits: u128,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
}

/// One compact joint-media consequence and every shared/local withdrawal returned together.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceJointMediaTransport {
    pub joint_anchor: Vec<u32>,
    pub shared_ablated_joint_anchor: Vec<u32>,
    /// Anchor-major, withdrawn-port-minor.
    pub local_ablated_joint_anchor: Vec<u32>,
    /// Family-major, port-major cells.
    pub predecessor_consequence: Vec<u32>,
    pub successor_consequence: Vec<u32>,
    pub shared_ablated_consequence: Vec<u32>,
    /// Cell-major, withdrawn-port-minor.
    pub local_ablated_consequence: Vec<u32>,
    pub anchors: usize,
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

/// R6's retained-context, derivation, and mathematical-media fronts after one resident typed
/// reduction.  Every alternative and withdrawal remains explicit; `selected_*` alone follows the
/// returned cultivation state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceProductionAperture {
    pub context_trace: Vec<u32>,
    pub context_boundary_withdrawn_trace: Vec<u32>,
    pub context_trace_stride: usize,
    pub derivation_predecessor_trace: Vec<u32>,
    pub derivation_successor_trace: Vec<u32>,
    pub derivation_selected_trace: Vec<u32>,
    pub derivation_generator_withdrawn_trace: Vec<u32>,
    pub derivation_predecessor_lengths: Vec<u32>,
    pub derivation_successor_lengths: Vec<u32>,
    pub derivation_selected_lengths: Vec<u32>,
    pub derivation_generator_withdrawn_lengths: Vec<u32>,
    pub derivation_trace_stride: usize,
    pub media_species_totals: Vec<u64>,
    pub media_shared_withdrawn_totals: Vec<u64>,
    /// Species-major, withdrawn-port-minor.
    pub media_local_withdrawn_totals: Vec<u64>,
    pub media_joint_anchors: u64,
    pub total_joint_incidence: u64,
    pub oriented_difference: i64,
    pub difference_magnitude: u64,
    pub difference_hand: i32,
    pub selected_cultivation_state: u32,
    pub context_fronts: usize,
    pub derivation_fronts: usize,
    pub media_anchors: usize,
    pub media_species: usize,
    pub media_ports: usize,
    pub committed: bool,
    pub launches: u64,
    pub synchronizations: u64,
    pub typed_reductions: u64,
    pub block_threads: u32,
    pub active_lanes: u32,
    pub semantic_work: u128,
    pub semantic_span: u64,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
}

/// Homogeneous quadratic sections transported through complete integer chart maps on the card.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceQuadraticSectionTransport {
    /// Section-major `(x^2, xy, y^2)` coefficient faces after substitution.
    pub transported_coefficients: Vec<i64>,
    pub invariant: Vec<u32>,
    /// `0` expanded coefficient route, `1` cultivated condensed route, `2` obstruction.
    pub selected_route: Vec<u32>,
    pub ablated_route: Vec<u32>,
    pub sections: usize,
    pub launches: u64,
    pub synchronizations: u64,
    pub block_threads: u32,
    pub active_lanes: u32,
    pub semantic_work: u128,
    pub semantic_span: u64,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
}

/// Multiple exact fixed-section families and their complete local/joint withdrawals returned from
/// one two-launch card passage.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceFixedSectionFamilies {
    /// Family-major exact returned coordinates.
    pub transported_sections: Vec<i64>,
    pub constraint_held: Vec<u32>,
    pub invariant: Vec<u32>,
    /// `0` expanded action, `1` cultivated fixed-section route, `2` obstruction.
    pub selected_route: Vec<u32>,
    pub ablated_route: Vec<u32>,
    pub joint_cultivated: bool,
    /// One entry per locally withdrawn family.
    pub local_ablated_joint: Vec<u32>,
    pub families: usize,
    pub dimension: usize,
    pub launches: u64,
    pub synchronizations: u64,
    pub typed_reductions: u64,
    pub block_threads: u32,
    pub active_lanes: u32,
    /// Family-major `[fixed-section, expanded-action]` work predictions derived only from the
    /// declared extents before dispatch. The card returns which alternative occurred.
    pub predicted_local_semantic_work: Vec<u64>,
    pub predicted_local_semantic_span: Vec<u64>,
    pub semantic_work: u128,
    pub semantic_span: u64,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
}

/// The fixed-section family after `A-I=L*C` has condensed its repeated dense actions into one
/// shared oriented generator relation. Carrier charts and returned-cultivation occurrences remain
/// plural; only the causally identical transport law is shared.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceNativeFixedSectionFamilies {
    pub transported_sections: Vec<i64>,
    pub constraint_residuals: Vec<i64>,
    pub constraint_held: Vec<u32>,
    pub invariant: Vec<u32>,
    /// `0` expanded native generator, `1` cultivated fixed-section route, `2` obstruction.
    pub selected_route: Vec<u32>,
    pub ablated_route: Vec<u32>,
    pub joint_cultivated: bool,
    pub local_ablated_joint: Vec<u32>,
    pub families: usize,
    pub dimension: usize,
    pub launches: u64,
    pub synchronizations: u64,
    pub typed_reductions: u64,
    pub block_threads: u32,
    pub active_lanes: u32,
    /// Family-major `[fixed-section, expanded-native-generator]` alternatives derived from the
    /// compact incidence extents before dispatch.
    pub predicted_local_semantic_work: Vec<u64>,
    pub predicted_local_semantic_span: Vec<u64>,
    pub semantic_work: u128,
    pub semantic_span: u64,
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

/// One complete pair population whose contact and simultaneous optical-role words were enacted
/// without a host boundary between the two resident laws. Each incidence word carries the
/// low-half left-to-right and high-half right-to-left relation masks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceOpticalIncidencePassage {
    pub contact_classes: Vec<u8>,
    pub incidence_words: Vec<u32>,
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

    /// Carry plural addressed words through one shared native action and return their exact
    /// ragged traces after one terminal synchronization.
    ///
    /// `word_offsets` is the canonical prefix-sum boundary of `words`, with one interval per
    /// starting occurrence.  Trace extents are therefore derived from the material word family;
    /// there is no padded context capacity and no host callback between steps.
    pub fn conduct_native_ragged_traces_on_device(
        &mut self,
        states: usize,
        generators: usize,
        generator_table: &[u32],
        words: &[u32],
        word_offsets: &[u32],
        native_start: &[u32],
    ) -> Result<DeviceRaggedNativeTrace, CudaRefineError> {
        let expected = states
            .checked_mul(generators)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let expected_offsets = native_start
            .len()
            .checked_add(1)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        if generator_table.len() != expected {
            return Err(CudaRefineError::NativeTableExtentDisagrees {
                table_entries: generator_table.len(),
                generators,
                states,
            });
        }
        if states == 0
            || generators == 0
            || native_start.is_empty()
            || word_offsets.len() != expected_offsets
            || word_offsets.first() != Some(&0)
            || word_offsets.last().copied() != u32::try_from(words.len()).ok()
            || word_offsets.windows(2).any(|pair| pair[0] > pair[1])
        {
            return Err(CudaRefineError::RaggedNativePassageShape);
        }
        if states > u32::MAX as usize
            || generators > u32::MAX as usize
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
        if let Some(generator) = words
            .iter()
            .copied()
            .find(|generator| *generator as usize >= generators)
        {
            return Err(CudaRefineError::NativeGeneratorOutsideFamily {
                generator,
                generators,
            });
        }

        let mut trace_offsets = Vec::with_capacity(expected_offsets);
        trace_offsets.push(0u32);
        for pair in word_offsets.windows(2) {
            let word_length = pair[1]
                .checked_sub(pair[0])
                .ok_or(CudaRefineError::RaggedNativePassageShape)?;
            let next = trace_offsets
                .last()
                .copied()
                .and_then(|offset| offset.checked_add(word_length)?.checked_add(1))
                .ok_or(CudaRefineError::NativeActionTooWide)?;
            trace_offsets.push(next);
        }
        let trace_entries = trace_offsets
            .last()
            .copied()
            .ok_or(CudaRefineError::RaggedNativePassageShape)? as usize;

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let table = Buffer::of(generator_table)?;
        let device_words = Buffer::of(words)?;
        let device_word_offsets = Buffer::of(word_offsets)?;
        let starts = Buffer::of(native_start)?;
        let device_trace_offsets = Buffer::of(&trace_offsets)?;
        let trace = Buffer::alloc(trace_entries * std::mem::size_of::<u32>())?;
        let grid = self.grid_for(native_start.len() as u64)?;
        let mut table_pointer = table.pointer;
        let mut words_pointer = device_words.pointer;
        let mut word_offsets_pointer = device_word_offsets.pointer;
        let mut starts_pointer = starts.pointer;
        let mut trace_offsets_pointer = device_trace_offsets.pointer;
        let mut trace_pointer = trace.pointer;
        let mut front_count = native_start.len() as u32;
        let mut state_count = states as u32;
        let mut arguments: [*mut c_void; 8] = [
            &mut table_pointer as *mut u64 as *mut c_void,
            &mut words_pointer as *mut u64 as *mut c_void,
            &mut word_offsets_pointer as *mut u64 as *mut c_void,
            &mut starts_pointer as *mut u64 as *mut c_void,
            &mut trace_offsets_pointer as *mut u64 as *mut c_void,
            &mut trace_pointer as *mut u64 as *mut c_void,
            &mut front_count as *mut u32 as *mut c_void,
            &mut state_count as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.native_ragged_trace,
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
            "cuLaunchKernel(conduct_native_ragged_trace)",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.launches += 1;

        let mut native_trace = vec![0u32; trace_entries];
        trace.read(&mut native_trace)?;
        let table_octets = std::mem::size_of_val(generator_table) as u64;
        let word_octets = std::mem::size_of_val(words) as u64;
        let offset_octets = std::mem::size_of_val(word_offsets) as u64;
        let start_octets = std::mem::size_of_val(native_start) as u64;
        let trace_offset_octets = std::mem::size_of_val(trace_offsets.as_slice()) as u64;
        let trace_octets = std::mem::size_of_val(native_trace.as_slice()) as u64;
        Ok(DeviceRaggedNativeTrace {
            native_trace,
            trace_offsets,
            front_count: native_start.len(),
            launches: 1,
            synchronizations: 1,
            block_threads: self.block_x,
            active_lanes: native_start.len() as u32,
            host_ingress_octets: table_octets
                + word_octets
                + offset_octets
                + start_octets
                + trace_offset_octets,
            host_egress_octets: trace_octets,
            resident_octets: table_octets
                + word_octets
                + offset_octets
                + start_octets
                + trace_offset_octets
                + trace_octets,
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

    /// Derive the complete candidate multiplicity of each source anchor/port cell on the card.
    /// Long exterior addresses have already crossed the codec mouth into exact local indices; the
    /// kernel visits every candidate for every cell and returns no winner or confidence quotient.
    pub fn derive_media_candidate_counts_on_device(
        &mut self,
        pair_anchor: &[u32],
        pair_port: &[u32],
        anchors: usize,
        ports: usize,
    ) -> Result<DeviceMediaCandidateCounts, CudaRefineError> {
        let cells = anchors
            .checked_mul(ports)
            .ok_or(CudaRefineError::JointMediaPassageShape)?;
        if anchors == 0
            || ports < 2
            || cells == 0
            || cells > u32::MAX as usize
            || pair_anchor.is_empty()
            || pair_anchor.len() != pair_port.len()
            || pair_anchor.len() > u32::MAX as usize
            || pair_anchor.iter().any(|anchor| *anchor as usize >= anchors)
            || pair_port.iter().any(|port| *port as usize >= ports)
        {
            return Err(CudaRefineError::JointMediaPassageShape);
        }

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let anchors_device = Buffer::of(pair_anchor)?;
        let ports_device = Buffer::of(pair_port)?;
        let count_octets = cells * std::mem::size_of::<u32>();
        let counts_device = Buffer::alloc(count_octets)?;
        let grid = self.grid_for(cells as u64)?;
        let mut anchor_pointer = anchors_device.pointer;
        let mut port_pointer = ports_device.pointer;
        let mut count_pointer = counts_device.pointer;
        let mut anchor_count = anchors as u32;
        let mut port_count = ports as u32;
        let mut pair_count = pair_anchor.len() as u32;
        let mut arguments: [*mut c_void; 6] = [
            &mut anchor_pointer as *mut u64 as *mut c_void,
            &mut port_pointer as *mut u64 as *mut c_void,
            &mut count_pointer as *mut u64 as *mut c_void,
            &mut anchor_count as *mut u32 as *mut c_void,
            &mut port_count as *mut u32 as *mut c_void,
            &mut pair_count as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.media_candidate_counts,
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
            "cuLaunchKernel(derive_media_candidate_counts)",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.launches += 1;
        let mut candidate_counts = vec![0u32; cells];
        counts_device.read(&mut candidate_counts)?;

        let anchor_octets = std::mem::size_of_val(pair_anchor) as u64;
        let port_octets = std::mem::size_of_val(pair_port) as u64;
        let scalar_octets = 3 * std::mem::size_of::<u32>() as u64;
        let semantic_pair_visits = (cells as u128)
            .checked_mul(pair_anchor.len() as u128)
            .ok_or(CudaRefineError::JointMediaPassageShape)?;
        Ok(DeviceMediaCandidateCounts {
            candidate_counts,
            anchors,
            ports,
            pairs: pair_anchor.len(),
            launches: 1,
            synchronizations: 1,
            block_threads: self.block_x,
            active_lanes: cells as u32,
            semantic_pair_visits,
            host_ingress_octets: anchor_octets + port_octets + scalar_octets,
            host_egress_octets: count_octets as u64,
            resident_octets: anchor_octets + port_octets + count_octets as u64,
        })
    }

    /// Enact one compact shared-media subcomplex and all its withdrawals in one resident front.
    #[allow(clippy::too_many_arguments)]
    pub fn conduct_joint_media_transport_on_device(
        &mut self,
        candidate_counts: &[u32],
        anchors: usize,
        successor_action: &[u32],
        decoder: &[u32],
        native_start: &[u32],
        families: usize,
        ports: usize,
    ) -> Result<DeviceJointMediaTransport, CudaRefineError> {
        let states = successor_action.len();
        let anchor_cells = anchors
            .checked_mul(ports)
            .ok_or(CudaRefineError::JointMediaPassageShape)?;
        let cells = families
            .checked_mul(ports)
            .ok_or(CudaRefineError::JointMediaPassageShape)?;
        let expected_decoder = cells
            .checked_mul(states)
            .ok_or(CudaRefineError::JointMediaPassageShape)?;
        let local_anchor_entries = anchor_cells;
        let local_entries = cells
            .checked_mul(ports)
            .ok_or(CudaRefineError::JointMediaPassageShape)?;
        let work = anchors.max(cells);
        if anchors == 0
            || families == 0
            || ports < 2
            || states == 0
            || work == 0
            || work > u32::MAX as usize
            || candidate_counts.len() != anchor_cells
            || candidate_counts.iter().any(|count| *count == 0)
            || decoder.len() != expected_decoder
            || native_start.len() != cells
            || successor_action
                .iter()
                .chain(native_start)
                .any(|state| *state as usize >= states)
        {
            return Err(CudaRefineError::JointMediaPassageShape);
        }

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let counts_device = Buffer::of(candidate_counts)?;
        let action_device = Buffer::of(successor_action)?;
        let decoder_device = Buffer::of(decoder)?;
        let starts_device = Buffer::of(native_start)?;
        let anchor_octets = anchors * std::mem::size_of::<u32>();
        let local_anchor_octets = local_anchor_entries * std::mem::size_of::<u32>();
        let cell_octets = cells * std::mem::size_of::<u32>();
        let local_octets = local_entries * std::mem::size_of::<u32>();
        let joint_device = Buffer::alloc(anchor_octets)?;
        let shared_joint_device = Buffer::alloc(anchor_octets)?;
        let local_joint_device = Buffer::alloc(local_anchor_octets)?;
        let predecessor_device = Buffer::alloc(cell_octets)?;
        let successor_device = Buffer::alloc(cell_octets)?;
        let shared_device = Buffer::alloc(cell_octets)?;
        let local_device = Buffer::alloc(local_octets)?;

        let grid = self.grid_for(work as u64)?;
        let mut counts_pointer = counts_device.pointer;
        let mut joint_pointer = joint_device.pointer;
        let mut shared_joint_pointer = shared_joint_device.pointer;
        let mut local_joint_pointer = local_joint_device.pointer;
        let mut anchor_count = anchors as u32;
        let mut action_pointer = action_device.pointer;
        let mut decoder_pointer = decoder_device.pointer;
        let mut starts_pointer = starts_device.pointer;
        let mut predecessor_pointer = predecessor_device.pointer;
        let mut successor_pointer = successor_device.pointer;
        let mut shared_pointer = shared_device.pointer;
        let mut local_pointer = local_device.pointer;
        let mut cell_count = cells as u32;
        let mut state_count = states as u32;
        let mut port_count = ports as u32;
        let mut arguments: [*mut c_void; 15] = [
            &mut counts_pointer as *mut u64 as *mut c_void,
            &mut joint_pointer as *mut u64 as *mut c_void,
            &mut shared_joint_pointer as *mut u64 as *mut c_void,
            &mut local_joint_pointer as *mut u64 as *mut c_void,
            &mut anchor_count as *mut u32 as *mut c_void,
            &mut action_pointer as *mut u64 as *mut c_void,
            &mut decoder_pointer as *mut u64 as *mut c_void,
            &mut starts_pointer as *mut u64 as *mut c_void,
            &mut predecessor_pointer as *mut u64 as *mut c_void,
            &mut successor_pointer as *mut u64 as *mut c_void,
            &mut shared_pointer as *mut u64 as *mut c_void,
            &mut local_pointer as *mut u64 as *mut c_void,
            &mut cell_count as *mut u32 as *mut c_void,
            &mut state_count as *mut u32 as *mut c_void,
            &mut port_count as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.joint_media_transport,
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
            "cuLaunchKernel(conduct_joint_media_transport)",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.launches += 1;

        let mut joint_anchor = vec![0u32; anchors];
        let mut shared_ablated_joint_anchor = vec![0u32; anchors];
        let mut local_ablated_joint_anchor = vec![0u32; local_anchor_entries];
        let mut predecessor_consequence = vec![0u32; cells];
        let mut successor_consequence = vec![0u32; cells];
        let mut shared_ablated_consequence = vec![0u32; cells];
        let mut local_ablated_consequence = vec![0u32; local_entries];
        joint_device.read(&mut joint_anchor)?;
        shared_joint_device.read(&mut shared_ablated_joint_anchor)?;
        local_joint_device.read(&mut local_ablated_joint_anchor)?;
        predecessor_device.read(&mut predecessor_consequence)?;
        successor_device.read(&mut successor_consequence)?;
        shared_device.read(&mut shared_ablated_consequence)?;
        local_device.read(&mut local_ablated_consequence)?;

        let count_octets = std::mem::size_of_val(candidate_counts) as u64;
        let action_octets = std::mem::size_of_val(successor_action) as u64;
        let decoder_octets = std::mem::size_of_val(decoder) as u64;
        let start_octets = std::mem::size_of_val(native_start) as u64;
        let scalar_octets = 4 * std::mem::size_of::<u32>() as u64;
        let returned_octets =
            (anchor_octets * 2 + local_anchor_octets + cell_octets * 3 + local_octets) as u64;
        Ok(DeviceJointMediaTransport {
            joint_anchor,
            shared_ablated_joint_anchor,
            local_ablated_joint_anchor,
            predecessor_consequence,
            successor_consequence,
            shared_ablated_consequence,
            local_ablated_consequence,
            anchors,
            families,
            ports,
            launches: 1,
            synchronizations: 1,
            block_threads: self.block_x,
            active_lanes: work as u32,
            host_ingress_octets: count_octets
                + action_octets
                + decoder_octets
                + start_octets
                + scalar_octets,
            host_egress_octets: returned_octets,
            resident_octets: count_octets
                + action_octets
                + decoder_octets
                + start_octets
                + returned_octets,
        })
    }

    /// Conduct R6's context, derivation, and mathematical-media fronts independently, then join
    /// only their complete exact returns through one typed reduction on the same CUDA stream.
    /// There is one synchronization after both launches and no host semantic callback between.
    #[allow(clippy::too_many_arguments)]
    pub fn conduct_production_aperture_on_device(
        &mut self,
        context_table: &[u32],
        context_states: usize,
        context_word: &[u32],
        context_start: &[u32],
        derivation_predecessor_action: &[u32],
        derivation_successor_action: &[u32],
        derivation_start: &[u32],
        media_candidate_species: &[u32],
        media_anchors: usize,
        media_species_port: &[u32],
        media_ports: usize,
        left_species: usize,
        right_species: usize,
        committed: bool,
    ) -> Result<DeviceProductionAperture, CudaRefineError> {
        let context_generators = context_table
            .len()
            .checked_div(context_states.max(1))
            .ok_or(CudaRefineError::ProductionApertureShape)?;
        let context_trace_stride = context_word
            .len()
            .checked_add(1)
            .ok_or(CudaRefineError::ProductionApertureShape)?;
        let context_trace_entries = context_start
            .len()
            .checked_mul(context_trace_stride)
            .ok_or(CudaRefineError::ProductionApertureShape)?;
        let derivation_states = derivation_predecessor_action.len();
        let derivation_trace_stride = derivation_states
            .checked_add(1)
            .ok_or(CudaRefineError::ProductionApertureShape)?;
        let derivation_trace_entries = derivation_start
            .len()
            .checked_mul(derivation_trace_stride)
            .ok_or(CudaRefineError::ProductionApertureShape)?;
        let media_species = media_species_port.len();
        let media_entries = media_anchors
            .checked_mul(media_species)
            .ok_or(CudaRefineError::ProductionApertureShape)?;
        let local_entries = media_species
            .checked_mul(media_ports)
            .ok_or(CudaRefineError::ProductionApertureShape)?;
        let active_lanes = context_start
            .len()
            .max(derivation_start.len())
            .max(media_anchors);
        let maximum_media_total = media_candidate_species
            .iter()
            .try_fold(0_u128, |total, value| total.checked_add(u128::from(*value)))
            .ok_or(CudaRefineError::ProductionApertureShape)?;
        if context_states == 0
            || context_table.len() != context_generators * context_states
            || context_generators < 2
            || context_word.is_empty()
            || context_start.len() < 2
            || context_states > u32::MAX as usize
            || context_word.len() > u32::MAX as usize
            || context_start.len() > u32::MAX as usize
            || context_table
                .iter()
                .any(|state| *state as usize >= context_states)
            || context_start
                .iter()
                .any(|state| *state as usize >= context_states)
            || context_word
                .iter()
                .any(|generator| *generator as usize >= context_generators)
            || derivation_states < 2
            || derivation_successor_action.len() != derivation_states
            || derivation_start.len() < 2
            || derivation_states > u32::MAX as usize
            || derivation_start.len() > u32::MAX as usize
            || derivation_predecessor_action
                .iter()
                .chain(derivation_successor_action)
                .chain(derivation_start)
                .any(|state| *state as usize >= derivation_states)
            || media_anchors == 0
            || media_species < 3
            || media_ports < 2
            || media_entries != media_candidate_species.len()
            || media_entries > u32::MAX as usize
            || media_candidate_species.iter().any(|count| *count == 0)
            || media_species_port
                .iter()
                .any(|port| *port as usize >= media_ports)
            || left_species >= media_species
            || right_species >= media_species
            || left_species == right_species
            || media_anchors > u32::MAX as usize
            || media_species > u32::MAX as usize
            || media_ports > u32::MAX as usize
            || active_lanes == 0
            || active_lanes > u32::MAX as usize
            || maximum_media_total > i64::MAX as u128
        {
            return Err(CudaRefineError::ProductionApertureShape);
        }

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let context_table_device = Buffer::of(context_table)?;
        let context_word_device = Buffer::of(context_word)?;
        let context_start_device = Buffer::of(context_start)?;
        let context_trace_octets = context_trace_entries * std::mem::size_of::<u32>();
        let context_trace_device = Buffer::alloc(context_trace_octets)?;
        let context_withdrawn_device = Buffer::alloc(context_trace_octets)?;

        let derivation_predecessor_device = Buffer::of(derivation_predecessor_action)?;
        let derivation_successor_device = Buffer::of(derivation_successor_action)?;
        let derivation_start_device = Buffer::of(derivation_start)?;
        let derivation_trace_octets = derivation_trace_entries * std::mem::size_of::<u32>();
        let derivation_predecessor_trace_device = Buffer::alloc(derivation_trace_octets)?;
        let derivation_successor_trace_device = Buffer::alloc(derivation_trace_octets)?;
        let derivation_selected_trace_device = Buffer::alloc(derivation_trace_octets)?;
        let derivation_generator_withdrawn_trace_device = Buffer::alloc(derivation_trace_octets)?;
        let derivation_length_octets = derivation_start.len() * std::mem::size_of::<u32>();
        let derivation_predecessor_length_device = Buffer::alloc(derivation_length_octets)?;
        let derivation_successor_length_device = Buffer::alloc(derivation_length_octets)?;
        let derivation_selected_length_device = Buffer::alloc(derivation_length_octets)?;
        let derivation_generator_withdrawn_length_device = Buffer::alloc(derivation_length_octets)?;

        let media_candidate_device = Buffer::of(media_candidate_species)?;
        let media_species_port_device = Buffer::of(media_species_port)?;
        let media_totals_octets = media_species * std::mem::size_of::<u64>();
        let media_totals_device = Buffer::alloc(media_totals_octets)?;
        media_totals_device.fill(0, media_totals_octets)?;
        let media_joint_device = Buffer::alloc(std::mem::size_of::<u64>())?;
        media_joint_device.fill(0, std::mem::size_of::<u64>())?;
        let media_shared_device = Buffer::alloc(media_totals_octets)?;
        let media_local_octets = local_entries * std::mem::size_of::<u64>();
        let media_local_device = Buffer::alloc(media_local_octets)?;
        let total_joint_device = Buffer::alloc(std::mem::size_of::<u64>())?;
        let oriented_difference_device = Buffer::alloc(std::mem::size_of::<i64>())?;
        let difference_magnitude_device = Buffer::alloc(std::mem::size_of::<u64>())?;
        let difference_hand_device = Buffer::alloc(std::mem::size_of::<i32>())?;
        let selected_cultivation_device = Buffer::alloc(std::mem::size_of::<u32>())?;

        let mut context_table_pointer = context_table_device.pointer;
        let mut context_word_pointer = context_word_device.pointer;
        let mut context_start_pointer = context_start_device.pointer;
        let mut context_trace_pointer = context_trace_device.pointer;
        let mut context_withdrawn_pointer = context_withdrawn_device.pointer;
        let mut context_cell_count = context_start.len() as u32;
        let mut context_state_count = context_states as u32;
        let mut context_word_length = context_word.len() as u32;
        let mut derivation_predecessor_pointer = derivation_predecessor_device.pointer;
        let mut derivation_successor_pointer = derivation_successor_device.pointer;
        let mut derivation_start_pointer = derivation_start_device.pointer;
        let mut derivation_predecessor_trace_pointer = derivation_predecessor_trace_device.pointer;
        let mut derivation_successor_trace_pointer = derivation_successor_trace_device.pointer;
        let mut derivation_selected_trace_pointer = derivation_selected_trace_device.pointer;
        let mut derivation_generator_withdrawn_trace_pointer =
            derivation_generator_withdrawn_trace_device.pointer;
        let mut derivation_predecessor_length_pointer =
            derivation_predecessor_length_device.pointer;
        let mut derivation_successor_length_pointer = derivation_successor_length_device.pointer;
        let mut derivation_selected_length_pointer = derivation_selected_length_device.pointer;
        let mut derivation_generator_withdrawn_length_pointer =
            derivation_generator_withdrawn_length_device.pointer;
        let mut derivation_cell_count = derivation_start.len() as u32;
        let mut derivation_state_count = derivation_states as u32;
        let mut media_candidate_pointer = media_candidate_device.pointer;
        let mut media_totals_pointer = media_totals_device.pointer;
        let mut media_joint_pointer = media_joint_device.pointer;
        let mut media_anchor_count = media_anchors as u32;
        let mut media_species_count = media_species as u32;
        let mut decision = u32::from(committed);
        let mut front_arguments: [*mut c_void; 27] = [
            &mut context_table_pointer as *mut u64 as *mut c_void,
            &mut context_word_pointer as *mut u64 as *mut c_void,
            &mut context_start_pointer as *mut u64 as *mut c_void,
            &mut context_trace_pointer as *mut u64 as *mut c_void,
            &mut context_withdrawn_pointer as *mut u64 as *mut c_void,
            &mut context_cell_count as *mut u32 as *mut c_void,
            &mut context_state_count as *mut u32 as *mut c_void,
            &mut context_word_length as *mut u32 as *mut c_void,
            &mut derivation_predecessor_pointer as *mut u64 as *mut c_void,
            &mut derivation_successor_pointer as *mut u64 as *mut c_void,
            &mut derivation_start_pointer as *mut u64 as *mut c_void,
            &mut derivation_predecessor_trace_pointer as *mut u64 as *mut c_void,
            &mut derivation_successor_trace_pointer as *mut u64 as *mut c_void,
            &mut derivation_selected_trace_pointer as *mut u64 as *mut c_void,
            &mut derivation_generator_withdrawn_trace_pointer as *mut u64 as *mut c_void,
            &mut derivation_predecessor_length_pointer as *mut u64 as *mut c_void,
            &mut derivation_successor_length_pointer as *mut u64 as *mut c_void,
            &mut derivation_selected_length_pointer as *mut u64 as *mut c_void,
            &mut derivation_generator_withdrawn_length_pointer as *mut u64 as *mut c_void,
            &mut derivation_cell_count as *mut u32 as *mut c_void,
            &mut derivation_state_count as *mut u32 as *mut c_void,
            &mut media_candidate_pointer as *mut u64 as *mut c_void,
            &mut media_totals_pointer as *mut u64 as *mut c_void,
            &mut media_joint_pointer as *mut u64 as *mut c_void,
            &mut media_anchor_count as *mut u32 as *mut c_void,
            &mut media_species_count as *mut u32 as *mut c_void,
            &mut decision as *mut u32 as *mut c_void,
        ];
        let grid = self.grid_for(active_lanes as u64)?;
        driver(
            unsafe {
                cuLaunchKernel(
                    self.production_aperture_fronts,
                    grid,
                    1,
                    1,
                    self.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    front_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(conduct_production_aperture_fronts)",
        )?;
        self.launches += 1;

        let mut media_species_port_pointer = media_species_port_device.pointer;
        let mut media_shared_pointer = media_shared_device.pointer;
        let mut media_local_pointer = media_local_device.pointer;
        let mut total_joint_pointer = total_joint_device.pointer;
        let mut oriented_difference_pointer = oriented_difference_device.pointer;
        let mut difference_magnitude_pointer = difference_magnitude_device.pointer;
        let mut difference_hand_pointer = difference_hand_device.pointer;
        let mut selected_cultivation_pointer = selected_cultivation_device.pointer;
        let mut media_port_count = media_ports as u32;
        let mut left = left_species as u32;
        let mut right = right_species as u32;
        let mut reduction_arguments: [*mut c_void; 14] = [
            &mut media_totals_pointer as *mut u64 as *mut c_void,
            &mut media_species_port_pointer as *mut u64 as *mut c_void,
            &mut media_shared_pointer as *mut u64 as *mut c_void,
            &mut media_local_pointer as *mut u64 as *mut c_void,
            &mut total_joint_pointer as *mut u64 as *mut c_void,
            &mut oriented_difference_pointer as *mut u64 as *mut c_void,
            &mut difference_magnitude_pointer as *mut u64 as *mut c_void,
            &mut difference_hand_pointer as *mut u64 as *mut c_void,
            &mut selected_cultivation_pointer as *mut u64 as *mut c_void,
            &mut media_species_count as *mut u32 as *mut c_void,
            &mut media_port_count as *mut u32 as *mut c_void,
            &mut left as *mut u32 as *mut c_void,
            &mut right as *mut u32 as *mut c_void,
            &mut decision as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.production_aperture_reduction,
                    1,
                    1,
                    1,
                    self.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    reduction_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(reduce_production_aperture_fronts)",
        )?;
        self.launches += 1;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;

        let mut context_trace = vec![0_u32; context_trace_entries];
        let mut context_boundary_withdrawn_trace = vec![0_u32; context_trace_entries];
        context_trace_device.read(&mut context_trace)?;
        context_withdrawn_device.read(&mut context_boundary_withdrawn_trace)?;
        let mut derivation_predecessor_trace = vec![0_u32; derivation_trace_entries];
        let mut derivation_successor_trace = vec![0_u32; derivation_trace_entries];
        let mut derivation_selected_trace = vec![0_u32; derivation_trace_entries];
        let mut derivation_generator_withdrawn_trace = vec![0_u32; derivation_trace_entries];
        derivation_predecessor_trace_device.read(&mut derivation_predecessor_trace)?;
        derivation_successor_trace_device.read(&mut derivation_successor_trace)?;
        derivation_selected_trace_device.read(&mut derivation_selected_trace)?;
        derivation_generator_withdrawn_trace_device
            .read(&mut derivation_generator_withdrawn_trace)?;
        let mut derivation_predecessor_lengths = vec![0_u32; derivation_start.len()];
        let mut derivation_successor_lengths = vec![0_u32; derivation_start.len()];
        let mut derivation_selected_lengths = vec![0_u32; derivation_start.len()];
        let mut derivation_generator_withdrawn_lengths = vec![0_u32; derivation_start.len()];
        derivation_predecessor_length_device.read(&mut derivation_predecessor_lengths)?;
        derivation_successor_length_device.read(&mut derivation_successor_lengths)?;
        derivation_selected_length_device.read(&mut derivation_selected_lengths)?;
        derivation_generator_withdrawn_length_device
            .read(&mut derivation_generator_withdrawn_lengths)?;
        if derivation_predecessor_lengths
            .iter()
            .chain(&derivation_successor_lengths)
            .chain(&derivation_selected_lengths)
            .chain(&derivation_generator_withdrawn_lengths)
            .any(|length| *length < 2 || *length as usize > derivation_trace_stride)
        {
            return Err(CudaRefineError::ProductionApertureShape);
        }
        let selected_expected = if committed {
            (&derivation_successor_trace, &derivation_successor_lengths)
        } else {
            (
                &derivation_predecessor_trace,
                &derivation_predecessor_lengths,
            )
        };
        if &derivation_selected_trace != selected_expected.0
            || &derivation_selected_lengths != selected_expected.1
        {
            return Err(CudaRefineError::ProductionApertureShape);
        }

        let mut media_species_totals = vec![0_u64; media_species];
        let mut media_shared_withdrawn_totals = vec![0_u64; media_species];
        let mut media_local_withdrawn_totals = vec![0_u64; local_entries];
        let mut media_joint_anchors = [0_u64];
        let mut total_joint_incidence = [0_u64];
        let mut oriented_difference = [0_i64];
        let mut difference_magnitude = [0_u64];
        let mut difference_hand = [0_i32];
        let mut selected_cultivation_state = [0_u32];
        media_totals_device.read(&mut media_species_totals)?;
        media_shared_device.read(&mut media_shared_withdrawn_totals)?;
        media_local_device.read(&mut media_local_withdrawn_totals)?;
        media_joint_device.read(&mut media_joint_anchors)?;
        total_joint_device.read(&mut total_joint_incidence)?;
        oriented_difference_device.read(&mut oriented_difference)?;
        difference_magnitude_device.read(&mut difference_magnitude)?;
        difference_hand_device.read(&mut difference_hand)?;
        selected_cultivation_device.read(&mut selected_cultivation_state)?;
        if media_joint_anchors[0] != media_anchors as u64
            || selected_cultivation_state[0] != u32::from(committed)
            || media_shared_withdrawn_totals
                .iter()
                .any(|value| *value != 0)
            || oriented_difference[0].unsigned_abs() != difference_magnitude[0]
            || oriented_difference[0].signum() != i64::from(difference_hand[0])
        {
            return Err(CudaRefineError::ProductionApertureShape);
        }

        let context_work = (context_start.len() as u128) * (context_word.len() as u128);
        let derivation_work =
            (derivation_start.len() as u128) * (derivation_states as u128) * 4_u128;
        let media_work = (media_anchors as u128) * (media_species as u128);
        let reduction_work = (media_species as u128) * (media_ports as u128 + 2_u128) + 5_u128;
        let semantic_work = context_work + derivation_work + media_work + reduction_work;
        let semantic_span = (context_word.len() as u64)
            .max(derivation_states as u64)
            .max((media_species * (media_ports + 2) + 5) as u64);
        let ingress = std::mem::size_of_val(context_table)
            + std::mem::size_of_val(context_word)
            + std::mem::size_of_val(context_start)
            + std::mem::size_of_val(derivation_predecessor_action)
            + std::mem::size_of_val(derivation_successor_action)
            + std::mem::size_of_val(derivation_start)
            + std::mem::size_of_val(media_candidate_species)
            + std::mem::size_of_val(media_species_port)
            + 12 * std::mem::size_of::<u32>();
        let egress = context_trace_octets * 2
            + derivation_trace_octets * 4
            + derivation_length_octets * 4
            + media_totals_octets * 2
            + media_local_octets
            + 3 * std::mem::size_of::<u64>()
            + std::mem::size_of::<i64>()
            + std::mem::size_of::<i32>()
            + std::mem::size_of::<u32>();
        let resident = ingress
            .checked_add(egress)
            .ok_or(CudaRefineError::ProductionApertureShape)?;
        Ok(DeviceProductionAperture {
            context_trace,
            context_boundary_withdrawn_trace,
            context_trace_stride,
            derivation_predecessor_trace,
            derivation_successor_trace,
            derivation_selected_trace,
            derivation_generator_withdrawn_trace,
            derivation_predecessor_lengths,
            derivation_successor_lengths,
            derivation_selected_lengths,
            derivation_generator_withdrawn_lengths,
            derivation_trace_stride,
            media_species_totals,
            media_shared_withdrawn_totals,
            media_local_withdrawn_totals,
            media_joint_anchors: media_joint_anchors[0],
            total_joint_incidence: total_joint_incidence[0],
            oriented_difference: oriented_difference[0],
            difference_magnitude: difference_magnitude[0],
            difference_hand: difference_hand[0],
            selected_cultivation_state: selected_cultivation_state[0],
            context_fronts: context_start.len(),
            derivation_fronts: derivation_start.len(),
            media_anchors,
            media_species,
            media_ports,
            committed,
            launches: 2,
            synchronizations: 1,
            typed_reductions: 1,
            block_threads: self.block_x,
            active_lanes: active_lanes as u32,
            semantic_work,
            semantic_span,
            host_ingress_octets: ingress as u64,
            host_egress_octets: egress as u64,
            resident_octets: resident as u64,
        })
    }

    /// Transport complete homogeneous quadratic sections through their integer chart maps on the
    /// card.  The host performs only an overflow/admission audit and verifies the returned device
    /// testimony; it does not select the semantic route.  `cultivated` is one caused standing bit
    /// crossing the front.  The card returns the expanded, condensed, and obstructed alternatives
    /// together so withdrawal does not require a replay.
    pub fn conduct_quadratic_sections_on_device(
        &mut self,
        coefficients: &[i64],
        transforms: &[i64],
        cultivated: bool,
    ) -> Result<DeviceQuadraticSectionTransport, CudaRefineError> {
        let sections = coefficients.len() / 3;
        if sections == 0
            || coefficients.len() != sections * 3
            || transforms.len() != sections * 4
            || sections > u32::MAX as usize
        {
            return Err(CudaRefineError::QuadraticTransportShape);
        }

        // The device law uses signed 64-bit integer arithmetic.  Establish that every
        // intermediate of the exact declared association fits before launch; this is an apparatus
        // admission audit, not a host implementation of the route decision.
        let product = |factors: &[i64]| -> Option<i64> {
            factors
                .iter()
                .try_fold(1_i64, |value, factor| value.checked_mul(*factor))
        };
        let mut expected = Vec::with_capacity(coefficients.len());
        for at in 0..sections {
            let coefficient_at = at * 3;
            let transform_at = at * 4;
            let a = coefficients[coefficient_at];
            let b = coefficients[coefficient_at + 1];
            let c = coefficients[coefficient_at + 2];
            let p = transforms[transform_at];
            let q = transforms[transform_at + 1];
            let r = transforms[transform_at + 2];
            let s = transforms[transform_at + 3];
            let returned_a = product(&[a, p, p])
                .and_then(|value| value.checked_add(product(&[b, p, r])?))
                .and_then(|value| value.checked_add(product(&[c, r, r])?));
            let returned_b = product(&[2, a, p, q])
                .and_then(|value| {
                    let mixed = product(&[p, s])?.checked_add(product(&[q, r])?)?;
                    value.checked_add(b.checked_mul(mixed)?)
                })
                .and_then(|value| value.checked_add(product(&[2, c, r, s])?));
            let returned_c = product(&[a, q, q])
                .and_then(|value| value.checked_add(product(&[b, q, s])?))
                .and_then(|value| value.checked_add(product(&[c, s, s])?));
            expected.extend([
                returned_a.ok_or(CudaRefineError::QuadraticTransportShape)?,
                returned_b.ok_or(CudaRefineError::QuadraticTransportShape)?,
                returned_c.ok_or(CudaRefineError::QuadraticTransportShape)?,
            ]);
        }

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let coefficient_device = Buffer::of(coefficients)?;
        let transform_device = Buffer::of(transforms)?;
        let coefficient_octets = std::mem::size_of_val(coefficients);
        let section_octets = sections * std::mem::size_of::<u32>();
        let transported_device = Buffer::alloc(coefficient_octets)?;
        let invariant_device = Buffer::alloc(section_octets)?;
        let selected_route_device = Buffer::alloc(section_octets)?;
        let ablated_route_device = Buffer::alloc(section_octets)?;
        let mut coefficient_pointer = coefficient_device.pointer;
        let mut transform_pointer = transform_device.pointer;
        let mut transported_pointer = transported_device.pointer;
        let mut invariant_pointer = invariant_device.pointer;
        let mut selected_route_pointer = selected_route_device.pointer;
        let mut ablated_route_pointer = ablated_route_device.pointer;
        let mut section_count = sections as u32;
        let mut cultivation = u32::from(cultivated);
        let mut arguments: [*mut c_void; 8] = [
            &mut coefficient_pointer as *mut u64 as *mut c_void,
            &mut transform_pointer as *mut u64 as *mut c_void,
            &mut transported_pointer as *mut u64 as *mut c_void,
            &mut invariant_pointer as *mut u64 as *mut c_void,
            &mut selected_route_pointer as *mut u64 as *mut c_void,
            &mut ablated_route_pointer as *mut u64 as *mut c_void,
            &mut section_count as *mut u32 as *mut c_void,
            &mut cultivation as *mut u32 as *mut c_void,
        ];
        let grid = self.grid_for(sections as u64)?;
        driver(
            unsafe {
                cuLaunchKernel(
                    self.quadratic_section_transport,
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
            "cuLaunchKernel(conduct_quadratic_section_transport)",
        )?;
        self.launches += 1;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;

        let mut transported_coefficients = vec![0_i64; coefficients.len()];
        let mut invariant = vec![0_u32; sections];
        let mut selected_route = vec![0_u32; sections];
        let mut ablated_route = vec![0_u32; sections];
        transported_device.read(&mut transported_coefficients)?;
        invariant_device.read(&mut invariant)?;
        selected_route_device.read(&mut selected_route)?;
        ablated_route_device.read(&mut ablated_route)?;
        let expected_invariant = expected
            .chunks_exact(3)
            .zip(coefficients.chunks_exact(3))
            .map(|(returned, entered)| u32::from(returned == entered))
            .collect::<Vec<_>>();
        let expected_selected = expected_invariant
            .iter()
            .enumerate()
            .map(|(at, held)| {
                let chart = &transforms[at * 4..at * 4 + 4];
                if cultivated && chart == [-1, 0, 0, -1] {
                    1
                } else if *held == 0 {
                    2
                } else {
                    0
                }
            })
            .collect::<Vec<_>>();
        let expected_ablated = expected_invariant
            .iter()
            .map(|held| if *held == 0 { 2 } else { 0 })
            .collect::<Vec<_>>();
        if transported_coefficients != expected
            || invariant != expected_invariant
            || selected_route != expected_selected
            || ablated_route != expected_ablated
        {
            return Err(CudaRefineError::QuadraticTransportShape);
        }

        let transform_octets = std::mem::size_of_val(transforms);
        let ingress = coefficient_octets + transform_octets + std::mem::size_of::<u32>();
        let egress = coefficient_octets + 3 * section_octets;
        let expanded_sections = expected_selected
            .iter()
            .filter(|route| **route != 1)
            .count();
        Ok(DeviceQuadraticSectionTransport {
            transported_coefficients,
            invariant,
            selected_route,
            ablated_route,
            sections,
            launches: 1,
            synchronizations: 1,
            block_threads: self.block_x,
            active_lanes: sections as u32,
            // Per expanded section: twenty-one exact products and seven exact sums.  The rested
            // central-inversion route transports its coefficient face without arithmetic.
            semantic_work: (expanded_sections as u128) * 28,
            // The condensed fixed-locus passage is one transport front; an expanded member keeps
            // the five-front coefficient dependency chain.
            semantic_span: if expanded_sections == 0 { 1 } else { 5 },
            host_ingress_octets: ingress as u64,
            host_egress_octets: egress as u64,
            resident_octets: (ingress + egress) as u64,
        })
    }

    /// Conduct several exact fixed-section families and join their complete route returns through
    /// one resident reduction.  Family and coordinate extents are derived from the supplied
    /// sections and modulus population.  A modulus of zero declares the integer carrier; every
    /// positive modulus must be at least two.
    #[allow(clippy::too_many_arguments)]
    pub fn conduct_fixed_section_families_on_device(
        &mut self,
        sections: &[i64],
        actions: &[i64],
        constraints: &[i64],
        constraint_rows: &[u32],
        moduli: &[i64],
        cultivated: &[u32],
    ) -> Result<DeviceFixedSectionFamilies, CudaRefineError> {
        let families = moduli.len();
        let dimension = sections.len().checked_div(families.max(1)).unwrap_or(0);
        let matrix_entries = families
            .checked_mul(dimension)
            .and_then(|extent| extent.checked_mul(dimension))
            .ok_or(CudaRefineError::FixedSectionFamilyShape)?;
        if families < 2
            || dimension == 0
            || sections.len() != families * dimension
            || actions.len() != matrix_entries
            || constraints.len() != matrix_entries
            || constraint_rows.len() != families
            || cultivated.len() != families
            || families > u32::MAX as usize
            || dimension > u32::MAX as usize
            || constraint_rows
                .iter()
                .any(|rows| *rows as usize > dimension)
            || moduli.iter().any(|modulus| *modulus < 0 || *modulus == 1)
            || cultivated.iter().any(|value| *value > 1)
        {
            return Err(CudaRefineError::FixedSectionFamilyShape);
        }
        let dimension_u64 =
            u64::try_from(dimension).map_err(|_| CudaRefineError::FixedSectionFamilyShape)?;
        let dot_work = dimension_u64
            .checked_mul(2)
            .and_then(|work| work.checked_sub(1))
            .ok_or(CudaRefineError::FixedSectionFamilyShape)?;
        let mut predicted_local_semantic_work = Vec::with_capacity(families * 2);
        let mut predicted_local_semantic_span = Vec::with_capacity(families * 2);
        for rows in constraint_rows {
            let rows = u64::from(*rows);
            let constraint_work = rows
                .checked_mul(dot_work)
                .ok_or(CudaRefineError::FixedSectionFamilyShape)?;
            let constraint_span = rows
                .checked_mul(dimension_u64)
                .ok_or(CudaRefineError::FixedSectionFamilyShape)?;
            predicted_local_semantic_work.push(constraint_work);
            predicted_local_semantic_work.push(
                constraint_work
                    .checked_add(
                        dimension_u64
                            .checked_mul(dot_work)
                            .ok_or(CudaRefineError::FixedSectionFamilyShape)?,
                    )
                    .ok_or(CudaRefineError::FixedSectionFamilyShape)?,
            );
            predicted_local_semantic_span.push(constraint_span);
            predicted_local_semantic_span.push(
                constraint_span
                    .checked_add(dimension_u64)
                    .ok_or(CudaRefineError::FixedSectionFamilyShape)?,
            );
        }

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let sections_device = Buffer::of(sections)?;
        let actions_device = Buffer::of(actions)?;
        let constraints_device = Buffer::of(constraints)?;
        let rows_device = Buffer::of(constraint_rows)?;
        let moduli_device = Buffer::of(moduli)?;
        let cultivated_device = Buffer::of(cultivated)?;
        let section_octets = std::mem::size_of_val(sections);
        let family_octets = families * std::mem::size_of::<u32>();
        let transported_device = Buffer::alloc(section_octets)?;
        let constraint_held_device = Buffer::alloc(family_octets)?;
        let invariant_device = Buffer::alloc(family_octets)?;
        let selected_route_device = Buffer::alloc(family_octets)?;
        let ablated_route_device = Buffer::alloc(family_octets)?;
        let local_measure_octets = families * std::mem::size_of::<u64>();
        let local_work_device = Buffer::alloc(local_measure_octets)?;
        let local_span_device = Buffer::alloc(local_measure_octets)?;
        let joint_device = Buffer::alloc(std::mem::size_of::<u32>())?;
        let local_joint_device = Buffer::alloc(family_octets)?;
        let work_device = Buffer::alloc(std::mem::size_of::<u64>())?;
        let span_device = Buffer::alloc(std::mem::size_of::<u64>())?;
        let mut sections_pointer = sections_device.pointer;
        let mut actions_pointer = actions_device.pointer;
        let mut constraints_pointer = constraints_device.pointer;
        let mut rows_pointer = rows_device.pointer;
        let mut moduli_pointer = moduli_device.pointer;
        let mut cultivated_pointer = cultivated_device.pointer;
        let mut transported_pointer = transported_device.pointer;
        let mut constraint_held_pointer = constraint_held_device.pointer;
        let mut invariant_pointer = invariant_device.pointer;
        let mut selected_route_pointer = selected_route_device.pointer;
        let mut ablated_route_pointer = ablated_route_device.pointer;
        let mut local_work_pointer = local_work_device.pointer;
        let mut local_span_pointer = local_span_device.pointer;
        let mut family_count = families as u32;
        let mut dimension_wire = dimension as u32;
        let mut arguments: [*mut c_void; 15] = [
            &mut sections_pointer as *mut u64 as *mut c_void,
            &mut actions_pointer as *mut u64 as *mut c_void,
            &mut constraints_pointer as *mut u64 as *mut c_void,
            &mut rows_pointer as *mut u64 as *mut c_void,
            &mut moduli_pointer as *mut u64 as *mut c_void,
            &mut cultivated_pointer as *mut u64 as *mut c_void,
            &mut transported_pointer as *mut u64 as *mut c_void,
            &mut constraint_held_pointer as *mut u64 as *mut c_void,
            &mut invariant_pointer as *mut u64 as *mut c_void,
            &mut selected_route_pointer as *mut u64 as *mut c_void,
            &mut ablated_route_pointer as *mut u64 as *mut c_void,
            &mut local_work_pointer as *mut u64 as *mut c_void,
            &mut local_span_pointer as *mut u64 as *mut c_void,
            &mut family_count as *mut u32 as *mut c_void,
            &mut dimension_wire as *mut u32 as *mut c_void,
        ];
        let grid = self.grid_for(families as u64)?;
        driver(
            unsafe {
                cuLaunchKernel(
                    self.fixed_section_families,
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
            "cuLaunchKernel(conduct_fixed_section_families)",
        )?;
        self.launches += 1;
        let mut joint_pointer = joint_device.pointer;
        let mut local_joint_pointer = local_joint_device.pointer;
        let mut work_pointer = work_device.pointer;
        let mut span_pointer = span_device.pointer;
        let mut reduction_arguments: [*mut c_void; 9] = [
            &mut selected_route_pointer as *mut u64 as *mut c_void,
            &mut ablated_route_pointer as *mut u64 as *mut c_void,
            &mut local_work_pointer as *mut u64 as *mut c_void,
            &mut local_span_pointer as *mut u64 as *mut c_void,
            &mut joint_pointer as *mut u64 as *mut c_void,
            &mut local_joint_pointer as *mut u64 as *mut c_void,
            &mut work_pointer as *mut u64 as *mut c_void,
            &mut span_pointer as *mut u64 as *mut c_void,
            &mut family_count as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.fixed_section_family_reduction,
                    1,
                    1,
                    1,
                    self.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    reduction_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(reduce_fixed_section_families)",
        )?;
        self.launches += 1;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;

        let mut transported_sections = vec![0_i64; sections.len()];
        let mut constraint_held = vec![0_u32; families];
        let mut invariant = vec![0_u32; families];
        let mut selected_route = vec![0_u32; families];
        let mut ablated_route = vec![0_u32; families];
        let mut local_semantic_work = vec![0_u64; families];
        let mut local_semantic_span = vec![0_u64; families];
        let mut joint_cultivated = [0_u32];
        let mut local_ablated_joint = vec![0_u32; families];
        let mut semantic_work = [0_u64];
        let mut semantic_span = [0_u64];
        transported_device.read(&mut transported_sections)?;
        constraint_held_device.read(&mut constraint_held)?;
        invariant_device.read(&mut invariant)?;
        selected_route_device.read(&mut selected_route)?;
        ablated_route_device.read(&mut ablated_route)?;
        local_work_device.read(&mut local_semantic_work)?;
        local_span_device.read(&mut local_semantic_span)?;
        joint_device.read(&mut joint_cultivated)?;
        local_joint_device.read(&mut local_ablated_joint)?;
        work_device.read(&mut semantic_work)?;
        span_device.read(&mut semantic_span)?;
        let reduction_work = u64::try_from(families)
            .ok()
            .and_then(|count| count.checked_add(count.checked_mul(count)?))
            .ok_or(CudaRefineError::FixedSectionFamilyShape)?;
        let predicted_returned_work = selected_route
            .iter()
            .enumerate()
            .try_fold(reduction_work, |work, (family, route)| {
                let alternative = usize::from(*route != 1);
                work.checked_add(predicted_local_semantic_work[family * 2 + alternative])
            })
            .ok_or(CudaRefineError::FixedSectionFamilyShape)?;
        let predicted_returned_span = selected_route
            .iter()
            .enumerate()
            .map(|(family, route)| {
                predicted_local_semantic_span[family * 2 + usize::from(*route != 1)]
            })
            .max()
            .and_then(|span| span.checked_add(families as u64))
            .ok_or(CudaRefineError::FixedSectionFamilyShape)?;
        if constraint_held.iter().any(|value| *value > 1)
            || invariant.iter().any(|value| *value > 1)
            || selected_route.iter().any(|value| *value > 2)
            || ablated_route.iter().any(|value| *value != 0 && *value != 2)
            || selected_route
                .iter()
                .enumerate()
                .any(|(family, route)| match *route {
                    0 => invariant[family] != 1,
                    1 => {
                        cultivated[family] != 1
                            || constraint_held[family] != 1
                            || invariant[family] != 1
                    }
                    2 => invariant[family] != 0,
                    _ => true,
                })
            || ablated_route
                .iter()
                .enumerate()
                .any(|(family, route)| *route != if invariant[family] == 1 { 0 } else { 2 })
            || joint_cultivated[0] > 1
            || local_ablated_joint.iter().any(|value| *value > 1)
            || (joint_cultivated[0] == 1) != selected_route.iter().all(|route| *route == 1)
            || local_ablated_joint
                .iter()
                .enumerate()
                .any(|(withdrawn, joint)| {
                    (*joint == 1)
                        != selected_route.iter().enumerate().all(|(family, route)| {
                            if family == withdrawn {
                                ablated_route[family] == 1
                            } else {
                                *route == 1
                            }
                        })
                })
            || local_semantic_work
                .iter()
                .zip(selected_route.iter().enumerate())
                .any(|(actual, (family, route))| {
                    *actual != predicted_local_semantic_work[family * 2 + usize::from(*route != 1)]
                })
            || local_semantic_span
                .iter()
                .zip(selected_route.iter().enumerate())
                .any(|(actual, (family, route))| {
                    *actual != predicted_local_semantic_span[family * 2 + usize::from(*route != 1)]
                })
            || semantic_work[0] != predicted_returned_work
            || semantic_span[0] != predicted_returned_span
        {
            return Err(CudaRefineError::FixedSectionFamilyShape);
        }
        let ingress = std::mem::size_of_val(sections)
            + std::mem::size_of_val(actions)
            + std::mem::size_of_val(constraints)
            + std::mem::size_of_val(constraint_rows)
            + std::mem::size_of_val(moduli)
            + std::mem::size_of_val(cultivated);
        let egress = section_octets
            + 5 * family_octets
            + 2 * local_measure_octets
            + std::mem::size_of::<u32>()
            + 2 * std::mem::size_of::<u64>();
        Ok(DeviceFixedSectionFamilies {
            transported_sections,
            constraint_held,
            invariant,
            selected_route,
            ablated_route,
            joint_cultivated: joint_cultivated[0] == 1,
            local_ablated_joint,
            families,
            dimension,
            launches: 2,
            synchronizations: 1,
            typed_reductions: 1,
            block_threads: self.block_x,
            active_lanes: families as u32,
            predicted_local_semantic_work,
            predicted_local_semantic_span,
            semantic_work: u128::from(semantic_work[0]),
            semantic_span: semantic_span[0],
            host_ingress_octets: ingress as u64,
            host_egress_octets: egress as u64,
            resident_octets: (ingress + egress) as u64,
        })
    }

    /// Conduct fixed-section families through one shared oriented relation `T = I + L*C`.
    ///
    /// The incidence orientations are mounted once for the complete family front. The card owns
    /// residual evaluation, native transport, cultivation/obstruction selection, joint return and
    /// every local ablation; the host validates the exact receipt after one synchronization.
    pub fn conduct_native_fixed_section_families_on_device(
        &mut self,
        sections: &[i64],
        constraint_orientation: &[i8],
        factor_orientation: &[i8],
        moduli: &[i64],
        cultivated: &[u32],
    ) -> Result<DeviceNativeFixedSectionFamilies, CudaRefineError> {
        let families = moduli.len();
        let dimension = sections.len().checked_div(families.max(1)).unwrap_or(0);
        if families < 2
            || dimension == 0
            || sections.len() != families * dimension
            || constraint_orientation.len() != dimension
            || factor_orientation.len() != dimension
            || constraint_orientation
                .iter()
                .chain(factor_orientation)
                .any(|orientation| !(-1..=1).contains(orientation))
            || !constraint_orientation
                .iter()
                .any(|orientation| *orientation != 0)
            || !factor_orientation
                .iter()
                .any(|orientation| *orientation != 0)
            || families > u32::MAX as usize
            || dimension > u32::MAX as usize
            || moduli.iter().any(|modulus| *modulus < 0 || *modulus == 1)
            || cultivated.iter().any(|value| *value > 1)
            || cultivated.len() != families
        {
            return Err(CudaRefineError::NativeFixedSectionFamilyShape);
        }
        let constraint_terms = constraint_orientation
            .iter()
            .filter(|orientation| **orientation != 0)
            .count() as u64;
        let factor_terms = factor_orientation
            .iter()
            .filter(|orientation| **orientation != 0)
            .count() as u64;
        let constraint_work = constraint_terms.saturating_sub(1);
        let constraint_span = constraint_work;
        let expanded_work = constraint_work
            .checked_add(factor_terms)
            .ok_or(CudaRefineError::NativeFixedSectionFamilyShape)?;
        let expanded_span = constraint_span
            .checked_add(u64::from(factor_terms != 0))
            .ok_or(CudaRefineError::NativeFixedSectionFamilyShape)?;
        let mut predicted_local_semantic_work = Vec::with_capacity(families * 2);
        let mut predicted_local_semantic_span = Vec::with_capacity(families * 2);
        for _ in 0..families {
            predicted_local_semantic_work.extend([constraint_work, expanded_work]);
            predicted_local_semantic_span.extend([constraint_span, expanded_span]);
        }

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let sections_device = Buffer::of(sections)?;
        let constraint_device = Buffer::of(constraint_orientation)?;
        let factor_device = Buffer::of(factor_orientation)?;
        let moduli_device = Buffer::of(moduli)?;
        let cultivated_device = Buffer::of(cultivated)?;
        let section_octets = std::mem::size_of_val(sections);
        let family_octets = families * std::mem::size_of::<u32>();
        let family_i64_octets = families * std::mem::size_of::<i64>();
        let local_measure_octets = families * std::mem::size_of::<u64>();
        let transported_device = Buffer::alloc(section_octets)?;
        let residual_device = Buffer::alloc(family_i64_octets)?;
        let constraint_held_device = Buffer::alloc(family_octets)?;
        let invariant_device = Buffer::alloc(family_octets)?;
        let selected_route_device = Buffer::alloc(family_octets)?;
        let ablated_route_device = Buffer::alloc(family_octets)?;
        let local_work_device = Buffer::alloc(local_measure_octets)?;
        let local_span_device = Buffer::alloc(local_measure_octets)?;
        let joint_device = Buffer::alloc(std::mem::size_of::<u32>())?;
        let local_joint_device = Buffer::alloc(family_octets)?;
        let work_device = Buffer::alloc(std::mem::size_of::<u64>())?;
        let span_device = Buffer::alloc(std::mem::size_of::<u64>())?;
        let mut sections_pointer = sections_device.pointer;
        let mut constraint_pointer = constraint_device.pointer;
        let mut factor_pointer = factor_device.pointer;
        let mut moduli_pointer = moduli_device.pointer;
        let mut cultivated_pointer = cultivated_device.pointer;
        let mut transported_pointer = transported_device.pointer;
        let mut residual_pointer = residual_device.pointer;
        let mut constraint_held_pointer = constraint_held_device.pointer;
        let mut invariant_pointer = invariant_device.pointer;
        let mut selected_route_pointer = selected_route_device.pointer;
        let mut ablated_route_pointer = ablated_route_device.pointer;
        let mut local_work_pointer = local_work_device.pointer;
        let mut local_span_pointer = local_span_device.pointer;
        let mut family_count = families as u32;
        let mut dimension_wire = dimension as u32;
        let mut arguments: [*mut c_void; 15] = [
            &mut sections_pointer as *mut u64 as *mut c_void,
            &mut constraint_pointer as *mut u64 as *mut c_void,
            &mut factor_pointer as *mut u64 as *mut c_void,
            &mut moduli_pointer as *mut u64 as *mut c_void,
            &mut cultivated_pointer as *mut u64 as *mut c_void,
            &mut transported_pointer as *mut u64 as *mut c_void,
            &mut residual_pointer as *mut u64 as *mut c_void,
            &mut constraint_held_pointer as *mut u64 as *mut c_void,
            &mut invariant_pointer as *mut u64 as *mut c_void,
            &mut selected_route_pointer as *mut u64 as *mut c_void,
            &mut ablated_route_pointer as *mut u64 as *mut c_void,
            &mut local_work_pointer as *mut u64 as *mut c_void,
            &mut local_span_pointer as *mut u64 as *mut c_void,
            &mut family_count as *mut u32 as *mut c_void,
            &mut dimension_wire as *mut u32 as *mut c_void,
        ];
        let grid = self.grid_for(families as u64)?;
        driver(
            unsafe {
                cuLaunchKernel(
                    self.native_fixed_section_families,
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
            "cuLaunchKernel(conduct_native_fixed_section_families)",
        )?;
        self.launches += 1;

        let mut joint_pointer = joint_device.pointer;
        let mut local_joint_pointer = local_joint_device.pointer;
        let mut work_pointer = work_device.pointer;
        let mut span_pointer = span_device.pointer;
        let mut reduction_arguments: [*mut c_void; 9] = [
            &mut selected_route_pointer as *mut u64 as *mut c_void,
            &mut ablated_route_pointer as *mut u64 as *mut c_void,
            &mut local_work_pointer as *mut u64 as *mut c_void,
            &mut local_span_pointer as *mut u64 as *mut c_void,
            &mut joint_pointer as *mut u64 as *mut c_void,
            &mut local_joint_pointer as *mut u64 as *mut c_void,
            &mut work_pointer as *mut u64 as *mut c_void,
            &mut span_pointer as *mut u64 as *mut c_void,
            &mut family_count as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.fixed_section_family_reduction,
                    1,
                    1,
                    1,
                    self.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    reduction_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(reduce_fixed_section_families)",
        )?;
        self.launches += 1;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;

        let mut transported_sections = vec![0_i64; sections.len()];
        let mut constraint_residuals = vec![0_i64; families];
        let mut constraint_held = vec![0_u32; families];
        let mut invariant = vec![0_u32; families];
        let mut selected_route = vec![0_u32; families];
        let mut ablated_route = vec![0_u32; families];
        let mut local_semantic_work = vec![0_u64; families];
        let mut local_semantic_span = vec![0_u64; families];
        let mut joint_cultivated = [0_u32];
        let mut local_ablated_joint = vec![0_u32; families];
        let mut semantic_work = [0_u64];
        let mut semantic_span = [0_u64];
        transported_device.read(&mut transported_sections)?;
        residual_device.read(&mut constraint_residuals)?;
        constraint_held_device.read(&mut constraint_held)?;
        invariant_device.read(&mut invariant)?;
        selected_route_device.read(&mut selected_route)?;
        ablated_route_device.read(&mut ablated_route)?;
        local_work_device.read(&mut local_semantic_work)?;
        local_span_device.read(&mut local_semantic_span)?;
        joint_device.read(&mut joint_cultivated)?;
        local_joint_device.read(&mut local_ablated_joint)?;
        work_device.read(&mut semantic_work)?;
        span_device.read(&mut semantic_span)?;

        let reduction_work = u64::try_from(families)
            .ok()
            .and_then(|count| count.checked_add(count.checked_mul(count)?))
            .ok_or(CudaRefineError::NativeFixedSectionFamilyShape)?;
        let predicted_returned_work = selected_route
            .iter()
            .enumerate()
            .try_fold(reduction_work, |work, (family, route)| {
                work.checked_add(
                    predicted_local_semantic_work[family * 2 + usize::from(*route != 1)],
                )
            })
            .ok_or(CudaRefineError::NativeFixedSectionFamilyShape)?;
        let predicted_returned_span = selected_route
            .iter()
            .enumerate()
            .map(|(family, route)| {
                predicted_local_semantic_span[family * 2 + usize::from(*route != 1)]
            })
            .max()
            .and_then(|span| span.checked_add(families as u64))
            .ok_or(CudaRefineError::NativeFixedSectionFamilyShape)?;
        if constraint_held.iter().any(|value| *value > 1)
            || invariant != constraint_held
            || selected_route.iter().any(|value| *value > 2)
            || ablated_route.iter().any(|value| *value != 0 && *value != 2)
            || selected_route
                .iter()
                .enumerate()
                .any(|(family, route)| match *route {
                    0 => invariant[family] != 1,
                    1 => cultivated[family] != 1 || invariant[family] != 1,
                    2 => invariant[family] != 0,
                    _ => true,
                })
            || ablated_route
                .iter()
                .enumerate()
                .any(|(family, route)| *route != if invariant[family] == 1 { 0 } else { 2 })
            || joint_cultivated[0] > 1
            || local_ablated_joint.iter().any(|value| *value > 1)
            || (joint_cultivated[0] == 1) != selected_route.iter().all(|route| *route == 1)
            || local_ablated_joint
                .iter()
                .enumerate()
                .any(|(withdrawn, joint)| {
                    (*joint == 1)
                        != selected_route.iter().enumerate().all(|(family, route)| {
                            if family == withdrawn {
                                ablated_route[family] == 1
                            } else {
                                *route == 1
                            }
                        })
                })
            || local_semantic_work
                .iter()
                .zip(selected_route.iter().enumerate())
                .any(|(actual, (family, route))| {
                    *actual != predicted_local_semantic_work[family * 2 + usize::from(*route != 1)]
                })
            || local_semantic_span
                .iter()
                .zip(selected_route.iter().enumerate())
                .any(|(actual, (family, route))| {
                    *actual != predicted_local_semantic_span[family * 2 + usize::from(*route != 1)]
                })
            || semantic_work[0] != predicted_returned_work
            || semantic_span[0] != predicted_returned_span
        {
            return Err(CudaRefineError::NativeFixedSectionFamilyShape);
        }
        let ingress = std::mem::size_of_val(sections)
            + std::mem::size_of_val(constraint_orientation)
            + std::mem::size_of_val(factor_orientation)
            + std::mem::size_of_val(moduli)
            + std::mem::size_of_val(cultivated);
        let egress = section_octets
            + family_i64_octets
            + 5 * family_octets
            + 2 * local_measure_octets
            + std::mem::size_of::<u32>()
            + 2 * std::mem::size_of::<u64>();
        Ok(DeviceNativeFixedSectionFamilies {
            transported_sections,
            constraint_residuals,
            constraint_held,
            invariant,
            selected_route,
            ablated_route,
            joint_cultivated: joint_cultivated[0] == 1,
            local_ablated_joint,
            families,
            dimension,
            launches: 2,
            synchronizations: 1,
            typed_reductions: 1,
            block_threads: self.block_x,
            active_lanes: families as u32,
            predicted_local_semantic_work,
            predicted_local_semantic_span,
            semantic_work: u128::from(semantic_work[0]),
            semantic_span: semantic_span[0],
            host_ingress_octets: ingress as u64,
            host_egress_octets: egress as u64,
            resident_octets: (ingress + egress) as u64,
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

    /// Return exact contact and every simultaneous local optical role without crossing a host
    /// boundary between the two laws. The caller supplies scale apertures read from the material;
    /// they are geometry receivers, not authored capacity bounds.
    pub fn optical_incidence_on_device(
        &mut self,
        lower_xyz: &[i64],
        upper_xyz: &[i64],
        task_left: &[u32],
        task_right: &[u32],
        aperture_squared: u64,
        term_gap: u64,
        line_gap: u64,
    ) -> Result<DeviceOpticalIncidencePassage, CudaRefineError> {
        if lower_xyz.len() != upper_xyz.len() || lower_xyz.len() % 3 != 0 {
            return Err(CudaRefineError::ContactCoordinateShape {
                lower: lower_xyz.len(),
                upper: upper_xyz.len(),
            });
        }
        if task_left.len() != task_right.len() {
            return Err(CudaRefineError::ContactIndexShape);
        }
        if term_gap > line_gap {
            return Err(CudaRefineError::OpticalIncidenceAperture { term_gap, line_gap });
        }
        let vertices = lower_xyz.len() / 3;
        if task_left.len() > u32::MAX as usize || vertices > u32::MAX as usize {
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

        let pair_count = task_left.len();
        if pair_count == 0 {
            return Ok(DeviceOpticalIncidencePassage {
                contact_classes: Vec::new(),
                incidence_words: Vec::new(),
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
        let incidences = Buffer::alloc(pair_count * std::mem::size_of::<u32>())?;

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

        let mut incidence_pointer = incidences.pointer;
        let mut term_gap_wire = term_gap;
        let mut line_gap_wire = line_gap;
        let mut incidence_arguments: Vec<*mut c_void> = vec![
            &mut lower_pointer as *mut u64 as *mut c_void,
            &mut upper_pointer as *mut u64 as *mut c_void,
            &mut left_pointer as *mut u64 as *mut c_void,
            &mut right_pointer as *mut u64 as *mut c_void,
            &mut class_pointer as *mut u64 as *mut c_void,
            &mut incidence_pointer as *mut u64 as *mut c_void,
            &mut pair_count_wire as *mut u32 as *mut c_void,
            &mut term_gap_wire as *mut u64 as *mut c_void,
            &mut line_gap_wire as *mut u64 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.optical_incidence,
                    self.grid_for(pair_count as u64)?,
                    1,
                    1,
                    self.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    incidence_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(classify_optical_incidence)",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.launches += 2;

        let mut contact_classes = vec![0_u8; pair_count];
        classes.read(&mut contact_classes)?;
        let mut incidence_words = vec![0_u32; pair_count];
        incidences.read(&mut incidence_words)?;
        let ingress = std::mem::size_of_val(lower_xyz)
            + std::mem::size_of_val(upper_xyz)
            + std::mem::size_of_val(task_left)
            + std::mem::size_of_val(task_right)
            + std::mem::size_of::<u64>() * 3;
        let egress = std::mem::size_of_val(contact_classes.as_slice())
            + std::mem::size_of_val(incidence_words.as_slice());
        Ok(DeviceOpticalIncidencePassage {
            contact_classes,
            incidence_words,
            launches: 2,
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

    /// Mounting separates invariant transport ingress from later addressed-state ingress.
    #[test]
    #[ignore = "requires the RTX CUDA device"]
    fn the_resident_native_word_is_not_reuploaded_between_successors() {
        let card = CudaRefineExecutor::new().expect("the card mounts");
        // One generator carries the two hands through three boundaries and then rests.
        let table = [2, 3, 4, 5, 4, 5];
        let mut word = ResidentNativeWord::mount(card, 6, 1, &table, &[0, 0])
            .expect("the native word mounts once");
        assert_eq!(word.mount_host_ingress_octets(), 32);
        let first = word.conduct(&[0, 1]).expect("the first successor returns");
        let second = word.conduct(&[1]).expect("the later successor returns");
        assert_eq!(first.native_end, vec![4, 5]);
        assert_eq!(second.native_end, vec![5]);
        assert_eq!(first.host_ingress_octets, 8);
        assert_eq!(second.host_ingress_octets, 4);
        assert!(!first.invariant_transport_reuploaded);
        assert!(!second.invariant_transport_reuploaded);
        assert_eq!(
            first.resident_invariant_octets,
            second.resident_invariant_octets
        );
    }

    /// The pre-quotient receiver keeps both phase coordinates and mounts its incidence only once.
    #[test]
    #[ignore = "requires the RTX CUDA device"]
    fn the_resident_complex_incidence_carries_phase_without_binary_collapse() {
        let card = CudaRefineExecutor::new().expect("the card mounts");
        let mut incidence =
            ResidentComplexIncidence::mount(card, "test/incidence", 0, 3, 2, &[1, 0, 2, 1, 0, 3])
                .expect("incidence mounts");
        let current = vec![
            ExactComplexWaveCurrent::one(),
            ExactComplexWaveCurrent::new(Rat::zero(), Rat::one()),
        ];
        let half_turn = current
            .iter()
            .map(ExactComplexWaveCurrent::negated)
            .collect::<Vec<_>>();
        let first = incidence
            .conduct(&[current.clone(), half_turn])
            .expect("complex fronts return");
        let later = incidence
            .conduct(&[current])
            .expect("later current returns");
        assert_eq!(
            first.sections[1],
            first.sections[0]
                .iter()
                .map(ExactComplexWaveCurrent::negated)
                .collect::<Vec<_>>()
        );
        assert_eq!(later.sections[0], first.sections[0]);
        assert_eq!(first.launches, 1);
        assert_eq!(later.launches, 1);
        assert!(!first.binary_receiver_taken);
        assert!(!first.invariant_transport_reuploaded);
        assert!(!later.invariant_transport_reuploaded);
        assert_eq!(
            first.resident_invariant_octets,
            later.resident_invariant_octets
        );
    }

    /// The exterior order receiver acts on a declared sufficient row cover and leaves a plural
    /// interval fibre unresolved rather than asking the host to select a row.
    #[test]
    #[ignore = "requires the RTX CUDA device"]
    fn the_resident_interval_potential_receiver_selects_and_retains_plurality_on_card() {
        let card = CudaRefineExecutor::new().expect("the card mounts");
        let mut receiver = ResidentIntervalPotentialReceiver::mount(
            card,
            "test/potential-cover",
            3,
            2,
            &[7, 11, 13],
            &[
                4, 0, // row 7
                0, 6, // row 11
                3, 3, // row 13
            ],
            &[
                5, 1, // row 7
                1, 7, // row 11
                4, 4, // row 13
            ],
        )
        .expect("receiver cover mounts");
        let returned = receiver
            .conduct(&[vec![Rat::one(), Rat::zero()], vec![Rat::zero(), Rat::one()]])
            .expect("receiver returns");
        assert_eq!(returned.selected_native_addresses, vec![7, 11]);
        assert_eq!(returned.selected_lower, vec!["4", "6"]);
        assert_eq!(returned.selected_upper, vec!["5", "7"]);
        assert_eq!(returned.plural_population, vec![2, 1]);
        assert!(!returned.invariant_transport_reuploaded);
        assert!(!returned.cpu_semantic_replay_after_device);
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

    /// R4's resident context passage: distinct causal words retain their own extents and order
    /// while the shared action crosses only once.
    #[test]
    #[ignore = "requires the RTX CUDA device"]
    fn the_card_returns_plural_ragged_words_without_reordering_them() {
        let mut card = CudaRefineExecutor::new().expect("the card mounts");
        // Generator 0 is the R3 predecessor action; generator 1 is its cultivated successor.
        let returned = card
            .conduct_native_ragged_traces_on_device(
                3,
                2,
                &[0, 0, 2, 2, 0, 2],
                &[0, 1, 1, 0, 1],
                &[0, 2, 4, 5],
                &[1, 1, 0],
            )
            .expect("the plural addressed words return");
        assert_eq!(returned.trace_offsets, vec![0, 3, 6, 8]);
        assert_eq!(&returned.native_trace[0..3], &[1, 0, 2]);
        assert_eq!(&returned.native_trace[3..6], &[1, 0, 0]);
        assert_eq!(&returned.native_trace[6..8], &[0, 2]);
        assert_ne!(returned.native_trace[2], returned.native_trace[5]);
        assert_eq!(returned.launches, 1);
        assert_eq!(returned.synchronizations, 1);
        assert_eq!(returned.active_lanes, 3);
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

    /// R5's joint-media law: the source candidate population is counted without a winner and the
    /// compact triadic subcomplex returns every shared/local withdrawal in one later front.
    #[test]
    #[ignore = "requires the RTX CUDA device"]
    fn the_card_derives_and_enacts_the_joint_media_subcomplex() {
        let mut card = CudaRefineExecutor::new().expect("the card mounts");
        let source = card
            .derive_media_candidate_counts_on_device(
                &[0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2],
                &[0, 1, 1, 2, 0, 1, 2, 2, 0, 1, 2],
                3,
                3,
            )
            .expect("the complete source candidates return");
        assert_eq!(source.candidate_counts, vec![1, 2, 1, 1, 1, 2, 1, 1, 1]);
        assert_eq!(source.semantic_pair_visits, 99);

        let returned = card
            .conduct_joint_media_transport_on_device(
                &source.candidate_counts,
                3,
                &[1, 1],
                &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
                &[0, 0, 0, 0, 0, 0],
                2,
                3,
            )
            .expect("the compact joint-media passage returns");
        assert_eq!(returned.joint_anchor, vec![1, 1, 1]);
        assert_eq!(returned.shared_ablated_joint_anchor, vec![0, 0, 0]);
        assert!(
            returned
                .local_ablated_joint_anchor
                .iter()
                .all(|value| *value == 0)
        );
        assert_eq!(returned.predecessor_consequence, vec![0, 2, 4, 6, 8, 10]);
        assert_eq!(returned.successor_consequence, vec![1, 3, 5, 7, 9, 11]);
        assert_eq!(returned.shared_ablated_consequence, vec![0, 2, 4, 6, 8, 10]);
        assert_eq!(returned.launches, 1);
        assert_eq!(returned.synchronizations, 1);
    }

    /// R6's fronts share no mutable standing and meet only after the exact card reduction.
    #[test]
    #[ignore = "requires the RTX CUDA device"]
    fn the_card_returns_the_bounded_production_aperture_without_a_host_semantic_bridge() {
        let mut card = CudaRefineExecutor::new().expect("the card mounts");
        let returned = card
            .conduct_production_aperture_on_device(
                &[0, 0, 2, 2, 0, 2],
                3,
                &[0, 1, 0, 1],
                &[0, 1, 2],
                &[0, 0, 2],
                &[2, 0, 2],
                &[0, 1],
                &[1, 2, 3, 2, 1, 4, 2, 1],
                2,
                &[0, 1, 2, 2],
                3,
                2,
                3,
                true,
            )
            .expect("the production passage returns");
        assert_eq!(returned.context_trace_stride, 5);
        assert_eq!(returned.media_species_totals, vec![2, 6, 5, 3]);
        assert_eq!(returned.total_joint_incidence, 16);
        assert_eq!(returned.oriented_difference, 2);
        assert_eq!(returned.difference_magnitude, 2);
        assert_eq!(returned.difference_hand, 1);
        assert_eq!(returned.selected_cultivation_state, 1);
        assert_eq!(
            returned.derivation_selected_trace,
            returned.derivation_successor_trace
        );
        assert_eq!(returned.launches, 2);
        assert_eq!(returned.synchronizations, 1);
        assert_eq!(returned.typed_reductions, 1);
    }

    /// L0's first cross-family cultivation: two distinct homogeneous quadratic sections retain
    /// their face under central inversion, while the mixed section under a single-axis reflection
    /// returns the shortest separating obstruction.  Withdrawal selects the expanded route without
    /// relaunching the law.
    #[test]
    #[ignore = "requires the RTX CUDA device"]
    fn the_card_cultivates_and_dissects_quadratic_section_transport() {
        let mut card = CudaRefineExecutor::new().expect("the card mounts");
        let returned = card
            .conduct_quadratic_sections_on_device(
                &[1, 0, -1, 1, 0, 1, 0, 1, 0],
                &[-1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, 1],
                true,
            )
            .expect("the quadratic sections return");
        assert_eq!(
            returned.transported_coefficients,
            vec![1, 0, -1, 1, 0, 1, 0, -1, 0]
        );
        assert_eq!(returned.invariant, vec![1, 1, 0]);
        assert_eq!(returned.selected_route, vec![1, 1, 2]);
        assert_eq!(returned.ablated_route, vec![0, 0, 2]);
        assert_eq!(returned.launches, 1);
        assert_eq!(returned.synchronizations, 1);
        assert_eq!(returned.semantic_work, 28);
        assert_eq!(returned.semantic_span, 5);
    }

    /// L1's common fixed-section law crosses an integer oriented-face family and an F2 additive
    /// coordinate family without routing on their exterior subjects.  Both local withdrawals
    /// reopen the composed route.
    #[test]
    #[ignore = "requires the RTX CUDA device"]
    fn the_card_joins_independent_fixed_section_families_and_returns_every_local_ablation() {
        let mut card = CudaRefineExecutor::new().expect("the card mounts");
        let action = [0, -1, 1, -1, 0, 1, 1, 1, 0];
        let constraints = [1, 1, -1, 0, 0, 0, 0, 0, 0];
        let expanded = card
            .conduct_fixed_section_families_on_device(
                &[7, -7, 0, 1, 0, 1],
                &[action, action].concat(),
                &[constraints, constraints].concat(),
                &[1, 1],
                &[0, 2],
                &[0, 0],
            )
            .expect("the expanded family returns");
        assert_eq!(expanded.transported_sections, vec![7, -7, 0, 1, 0, 1]);
        assert_eq!(expanded.selected_route, vec![0, 0]);
        assert!(!expanded.joint_cultivated);
        assert_eq!(expanded.semantic_work, 46);

        let cultivated = card
            .conduct_fixed_section_families_on_device(
                &[7, -7, 0, 1, 0, 1],
                &[action, action].concat(),
                &[constraints, constraints].concat(),
                &[1, 1],
                &[0, 2],
                &[1, 1],
            )
            .expect("the cultivated family returns");
        assert_eq!(cultivated.constraint_held, vec![1, 1]);
        assert_eq!(cultivated.invariant, vec![1, 1]);
        assert_eq!(cultivated.selected_route, vec![1, 1]);
        assert_eq!(cultivated.ablated_route, vec![0, 0]);
        assert!(cultivated.joint_cultivated);
        assert_eq!(cultivated.local_ablated_joint, vec![0, 0]);
        assert_eq!(cultivated.semantic_work, 16);
        assert_eq!(cultivated.semantic_span, 5);
        assert_eq!(cultivated.predicted_local_semantic_work, vec![5, 20, 5, 20]);
        assert_eq!(cultivated.predicted_local_semantic_span, vec![3, 6, 3, 6]);
        assert_eq!(
            cultivated.host_ingress_octets + cultivated.host_egress_octets,
            508
        );
        assert_eq!(cultivated.launches, 2);
        assert_eq!(cultivated.synchronizations, 1);
        assert_eq!(cultivated.typed_reductions, 1);
    }

    /// L2 rests the repeated dense action as one oriented relation `T=I+L*C`.  The equal present
    /// zero sections remain in distinct carrier charts, and `[1,1,0]` is their first admitted
    /// future separator: its integer residual is two while its F2 residual vanishes.
    #[test]
    #[ignore = "requires the RTX CUDA device"]
    fn the_card_conducts_the_native_fixed_section_relation_and_reopens_the_carrier_fibre() {
        let mut card = CudaRefineExecutor::new().expect("the card mounts");
        let cultivated = card
            .conduct_native_fixed_section_families_on_device(
                &[11, -11, 0, 1, 1, 0],
                &[1, 1, -1],
                &[-1, -1, 1],
                &[0, 2],
                &[1, 1],
            )
            .expect("the native family returns");
        assert_eq!(cultivated.constraint_residuals, vec![0, 0]);
        assert_eq!(cultivated.selected_route, vec![1, 1]);
        assert!(cultivated.joint_cultivated);
        assert_eq!(cultivated.local_ablated_joint, vec![0, 0]);
        assert_eq!(cultivated.semantic_work, 10);
        assert_eq!(cultivated.semantic_span, 4);
        assert_eq!(cultivated.predicted_local_semantic_work, vec![2, 5, 2, 5]);
        assert_eq!(cultivated.predicted_local_semantic_span, vec![2, 3, 2, 3]);
        assert_eq!(
            cultivated.host_ingress_octets + cultivated.host_egress_octets,
            234
        );

        let reopened = card
            .conduct_native_fixed_section_families_on_device(
                &[1, 1, 0, 1, 1, 0],
                &[1, 1, -1],
                &[-1, -1, 1],
                &[0, 2],
                &[1, 1],
            )
            .expect("the carrier separator returns");
        assert_eq!(reopened.constraint_residuals, vec![2, 0]);
        assert_eq!(reopened.transported_sections, vec![-1, -1, 2, 1, 1, 0]);
        assert_eq!(reopened.selected_route, vec![2, 1]);
        assert!(!reopened.joint_cultivated);
        assert_eq!(reopened.semantic_work, 13);
        assert_eq!(reopened.semantic_span, 5);
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
